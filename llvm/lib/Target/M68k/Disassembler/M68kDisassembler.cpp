//===- M68kDisassembler.cpp - Disassembler for M68k -------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file is part of the M68k Disassembler.
//
//===----------------------------------------------------------------------===//

#include "M68k.h"
#include "M68kRegisterInfo.h"
#include "M68kSubtarget.h"
#include "MCTargetDesc/M68kMCTargetDesc.h"
#include "MCTargetDesc/M68kMCCodeEmitter.h"
#include "TargetInfo/M68kTargetInfo.h"

#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCDisassembler/MCDisassembler.h"
#include "llvm/MC/MCInst.h"
#include "llvm/Support/TargetRegistry.h"

using namespace llvm;

#define DEBUG_TYPE "m68k-disassembler"

typedef MCDisassembler::DecodeStatus DecodeStatus;

namespace {
constexpr unsigned MaxInstructionWords = 11;

class M68kInstructionBuffer {
  typedef SmallVector<uint16_t, MaxInstructionWords> BufferType;
  BufferType Buffer;

public:
  M68kInstructionBuffer() {}

  template<typename TIt>
  M68kInstructionBuffer(TIt Start, TIt End)
    : Buffer(Start, End) {}

  unsigned size() const { return Buffer.size(); }

  BufferType::const_iterator begin() const { return Buffer.begin(); }
  BufferType::const_iterator end() const { return Buffer.end(); }

  uint16_t operator[](unsigned Index) const {
    assert((Index < Buffer.size()) && "tried to read out of bounds word");
    return Buffer[Index];
  }

  void truncate(unsigned NewLength) {
    assert((NewLength <= Buffer.size()) && "instruction buffer too short to truncate");
    Buffer.resize(NewLength);
  }

  void dump() const {
    for (unsigned I = 0; I < Buffer.size(); ++I) {
      for (unsigned B = 0; B < 16; ++B) {
        uint16_t Bit = (1 << (16 - B - 1));
        unsigned IsClear = !(Buffer[I] & Bit);

        if (B == 8) {
          dbgs() << " ";
        }

        char Ch = IsClear ? '0' : '1';
        dbgs() << Ch;
      }

      dbgs() << " ";
    }

    dbgs() << "\n";
  }

  static M68kInstructionBuffer fill(ArrayRef<uint8_t> Bytes) {
    SmallVector<uint16_t, MaxInstructionWords> Buffer;
    Buffer.resize(std::min(Bytes.size() / 2, Buffer.max_size()));

    for (unsigned I = 0; I < Buffer.size(); ++I) {
      unsigned Offset = I * 2;
      uint64_t Hi = Bytes[Offset];
      uint64_t Lo = Bytes[Offset + 1];
      uint64_t Word = (Hi << 8) | Lo;
      Buffer[I] = Word;

      LLVM_DEBUG(errs() << format("Read word %x (%d)\n", (unsigned)Word, Buffer.size()));
    }

    return M68kInstructionBuffer(Buffer.begin(), Buffer.end());
  }
};

class M68kInstructionReader {
  M68kInstructionBuffer Buffer;
  unsigned NumRead;

public:
  M68kInstructionReader(M68kInstructionBuffer Buf)
    : Buffer(Buf), NumRead(0) {}

  unsigned size() const {
    return (Buffer.size() * 16) - NumRead;
  }

  uint64_t readBits(unsigned NumBits) {
    assert((size() >= NumBits) && "not enough bits to read");

    // We have to read the bits in 16-bit chunks because we read them as
    // 16-bit words but they're actually written in big-endian. If a read
    // crosses a word boundary we have to be careful.

    uint64_t Value = 0;
    while (NumBits > 0) {
      unsigned AvailableThisWord = 16 - (NumRead & 0xf);
      unsigned ToRead = std::min(NumBits, AvailableThisWord);

      unsigned WordIndex = NumRead >> 4;
      uint64_t ThisWord = Buffer[WordIndex];
      uint64_t Mask = (1 << ToRead) - 1;
      Value = (Value << ToRead) | (ThisWord & Mask);
      NumRead += ToRead;
      NumBits -= ToRead;
    }
    return Value;
  }
};

struct M68kInstructionLookup {
  unsigned OpCode;
  M68kInstructionBuffer Mask;
  M68kInstructionBuffer Value;

  unsigned size() const { return Mask.size(); }

  // Check whether this instruction could possibly match the given bytes.
  bool matches(const M68kInstructionBuffer &Test) const {
    if (Test.size() < Value.size()) {
      return false;
    }

    for (unsigned I = 0; I < Value.size(); ++I) {
      uint16_t Have = Test[I];
      uint16_t Need = Value[I];
      uint16_t WordMask = Mask[I];

      if ((Have & WordMask) != Need) {
        return false;
      }
    }

    return true;
  }

  void dump() const {
    dbgs() << "M68kInstructionLookup " << OpCode << " ";

    for (unsigned I = 0; I < Mask.size(); ++I) {
      uint16_t WordMask = Mask[I];
      uint16_t WordValue = Value[I];

      for (unsigned B = 0; B < 16; ++B) {
        uint16_t Bit = (1 << (15 - B));
        unsigned IsMasked = !(WordMask & Bit);
        unsigned IsClear = !(WordValue & Bit);

        if (B == 8) {
          dbgs() << " ";
        }

        char Ch = IsMasked ? '?' : (IsClear ? '0' : '1');
        dbgs() << Ch;
      }

      dbgs() << " ";
    }

    dbgs() << "\n";
  }
};

class M68kInstructionLookupBuilder {
  std::array<uint16_t, MaxInstructionWords> Mask;
  std::array<uint16_t, MaxInstructionWords> Value;
  unsigned NumWritten;

public:
  M68kInstructionLookupBuilder(): NumWritten(0) {
    Mask.fill(0);
    Value.fill(0);
  }

  unsigned numWords() const {
    assert(!(NumWritten & 0xf) && "instructions must be whole words");
    return NumWritten >> 4;
  }

  bool isValid() const {
    for (unsigned I = 0; I < numWords(); ++I) {
      if (Mask[I]) {
        return true;
      }
    }

    return false;
  }

  M68kInstructionLookup build(unsigned OpCode) {
    unsigned NumWords = numWords();
    M68kInstructionBuffer MaskBuffer(Mask.begin(), Mask.begin() + NumWords);
    M68kInstructionBuffer ValueBuffer(Value.begin(), Value.begin() + NumWords);
    M68kInstructionLookup Ret;
    Ret.OpCode = OpCode;
    Ret.Mask = MaskBuffer;
    Ret.Value = ValueBuffer;
    return Ret;
  }

  void addBits(unsigned N, uint64_t Bits) {
    while (N > 0) {
      unsigned WordIndex = NumWritten >> 4;
      unsigned WordOffset = NumWritten & 0xf;
      unsigned AvailableThisWord = 16 - WordOffset;
      unsigned ToWrite = std::min(AvailableThisWord, N);

      uint16_t WordMask = (1 << ToWrite) - 1;
      uint16_t BitsToWrite = Bits & WordMask;

      Value[WordIndex] |= (BitsToWrite << WordOffset);
      Mask[WordIndex] |= (WordMask << WordOffset);

      Bits >>= ToWrite;
      N -= ToWrite;
      NumWritten += ToWrite;
    }
  }

  void skipBits(unsigned N) {
    NumWritten += N;
  }
};

/// A disassembler class for M68k.
class M68kDisassembler : public MCDisassembler {
  MCInstrInfo* MCII;
  std::vector<M68kInstructionLookup> Lookups;

public:
  M68kDisassembler(const MCSubtargetInfo &STI, MCContext &Ctx, MCInstrInfo* MCII)
      : MCDisassembler(STI, Ctx), MCII(MCII) {
    buildBeadTable();
  }
  virtual ~M68kDisassembler() {}

  void buildBeadTable();
  DecodeStatus getInstruction(MCInst &Instr, uint64_t &Size,
                              ArrayRef<uint8_t> Bytes, uint64_t Address,
                              raw_ostream &CStream) const override;
  void decodeReg(MCInst &Instr, unsigned int Bead,
                 M68kInstructionReader &Reader, unsigned &Scratch) const;
  void decodeImm(MCInst &Instr, unsigned int Bead,
                 M68kInstructionReader &Reader, unsigned &Scratch) const;
  unsigned int getRegOperandIndex(MCInst &Instr, unsigned int Bead) const;
  unsigned int getImmOperandIndex(MCInst &Instr, unsigned int Bead) const;
};

static unsigned RegisterDecode[] = {
    M68k::A0, M68k::A1, M68k::A2, M68k::A3,
    M68k::A4, M68k::A5, M68k::A6, M68k::SP,
    M68k::D0, M68k::D1, M68k::D2, M68k::D3,
    M68k::D4, M68k::D5, M68k::D6, M68k::D7,
};

} // namespace

// This is a bit of a hack: we can't generate this table at table-gen time
// because some of the definitions are in our platform.
void M68kDisassembler::buildBeadTable() {
  const unsigned NumInstr = M68k::getNumMCInstrBeads();
  Lookups.reserve(NumInstr);

  for (unsigned I = 0; I < NumInstr; ++I) {
    M68kInstructionLookupBuilder Builder;

    for (const uint8_t* PartPtr = M68k::getMCInstrBeads(I);
         *PartPtr; ++PartPtr) {
      uint8_t Bead = *PartPtr;
      unsigned Ext = Bead >> 4;
      unsigned Op = Bead & 0xf;

      switch (Op) {
      case M68kBeads::Ctrl:
        switch (Ext) {
        case M68kBeads::Ignore:
          continue;

        default:
          // Term will have already been skipped by the loop.
          llvm_unreachable("unexpected command bead");
        }

      case M68kBeads::Bits1:
        Builder.addBits(1, Ext);
        break;

      case M68kBeads::Bits2:
        Builder.addBits(2, Ext);
        break;

      case M68kBeads::Bits3:
        Builder.addBits(3, Ext);
        break;

      case M68kBeads::Bits4:
        Builder.addBits(4, Ext);
        break;

      case M68kBeads::DAReg:
      case M68kBeads::DA:
      case M68kBeads::DReg:
      case M68kBeads::Reg:
        if (Op != M68kBeads::DA) {
          Builder.skipBits(3);
        }

        if (Op != M68kBeads::Reg && Op != M68kBeads::DReg) {
          Builder.skipBits(1);
        }
        break;

      case M68kBeads::Disp8:
        Builder.skipBits(8);
        break;

      case M68kBeads::Imm8:
      case M68kBeads::Imm16:
        Builder.skipBits(16);
        break;

      case M68kBeads::Imm32:
        Builder.skipBits(32);
        break;

      case M68kBeads::Imm3:
        Builder.skipBits(3);
        break;

      default:
        llvm_unreachable("unhandled bead type");
      }
    }

    // Ignore instructions which are unmatchable (usually pseudo instructions).
    if (!Builder.isValid()) {
      continue;
    }

    Lookups.push_back(Builder.build(I));
  }

#if 0
//#ifndef NDEBUG
  // TODO: This doesn't work because multiple instructions can have the same
  // machine code output. :(
  for (unsigned I = 0; I < NumInstr; ++I) {
    M68kInstructionLookup LookupA = Lookups[I];
    for (unsigned J = 0; J < NumInstr; ++J) {
      if (J == I) {
        continue;
      }

      M68kInstructionLookup LookupB = Lookups[J];
      if ((LookupA.Mask & LookupB.Mask) != LookupA.Mask) {
        continue;
      }

      if (LookupA.Value == LookupB.Value) {
        StringRef NameA = MCII->getName(LookupA.OpCode);
        StringRef NameB = MCII->getName(LookupB.OpCode);

        llvm::errs() << "multiple instructions with the same mask: \n"
          << "  " << NameA << " and " << NameB << "\n"
          << llvm::format("  %x %x", LookupA.Value, LookupB.Value) << "\n"
          << llvm::format("  %x %x", LookupA.Mask, LookupB.Mask) << "\n";

        llvm::errs() << "Beads: \n  ";
        for (const uint8_t *BeadPtr = M68k::getMCInstrBeads(LookupA.OpCode); *BeadPtr; ++BeadPtr) {
          llvm::errs() << format("%02x ", (unsigned)*BeadPtr);
        }
        llvm::errs() << "\n  ";
        for (const uint8_t *BeadPtr = M68k::getMCInstrBeads(LookupB.OpCode); *BeadPtr; ++BeadPtr) {
          llvm::errs() << format("%02x ", (unsigned)*BeadPtr);
        }
        llvm::errs() << "\n";
      }

      assert((LookupA.Value != LookupB.Value)
             && "Multiple instructions with the same mask");
    }
  }

#endif
}

unsigned M68kDisassembler::getRegOperandIndex(MCInst &Instr, unsigned Bead) const {
  auto Ext = Bead >> 4;

  const MCInstrDesc &Desc = MCII->get(Instr.getOpcode());
  auto MIOpIdx = M68k::getLogicalOperandIdx(Instr.getOpcode(), Ext & 7);

  if (M68kII::hasMultiMIOperands(Instr.getOpcode(), Ext & 7)) {
    bool IsPCRel = Desc.OpInfo[MIOpIdx].OperandType == MCOI::OPERAND_PCREL;
    if (IsPCRel) {
      MIOpIdx += M68k::PCRelIndex;
    } else if (Ext & 8) {
      MIOpIdx += M68k::MemIndex;
    } else {
      MIOpIdx += M68k::MemBase;
    }
  }

  return MIOpIdx;
}

unsigned M68kDisassembler::getImmOperandIndex(MCInst &Instr, unsigned Bead) const {
  auto Ext = Bead >> 4;

  const MCInstrDesc &Desc = MCII->get(Instr.getOpcode());
  auto MIOpIdx = M68k::getLogicalOperandIdx(Instr.getOpcode(), Ext & 7);

  if (M68kII::hasMultiMIOperands(Instr.getOpcode(), Ext & 7)) {
    bool IsPCRel = Desc.OpInfo[MIOpIdx].OperandType == MCOI::OPERAND_PCREL;
    if (IsPCRel) {
      MIOpIdx += M68k::PCRelDisp;
    } else if (Ext & 8) {
      MIOpIdx += M68k::MemOuter;
    } else {
      MIOpIdx += M68k::MemDisp;
    }
  }

  return MIOpIdx;
}

void M68kDisassembler::decodeReg(MCInst &Instr, unsigned Bead,
                                 M68kInstructionReader &Reader,
                                 unsigned &Scratch) const {
  unsigned Op = Bead & 0xf;
  LLVM_DEBUG(errs() << format("decodeReg %x\n", Bead));

  if (Op != M68kBeads::DA) {
    Scratch = (Scratch &~ 7) | Reader.readBits(3);
  }

  if (Op != M68kBeads::Reg) {
    bool DA = (Op != M68kBeads::DReg) && Reader.readBits(1);
    if (!DA) {
      Scratch |= 8;
    } else {
      Scratch &=~ 8;
    }
  }
}

void M68kDisassembler::decodeImm(MCInst &Instr, unsigned Bead,
                                 M68kInstructionReader &Reader,
                                 unsigned &Scratch) const {
  unsigned Op = Bead & 0xf;
  LLVM_DEBUG(errs() << format("decodeImm %x\n", Bead));

  unsigned NumToRead;
  switch (Op) {
  case M68kBeads::Disp8:
    NumToRead = 8;
    break;
  case M68kBeads::Imm8:
  case M68kBeads::Imm16:
    NumToRead = 16;
    break;
  case M68kBeads::Imm32:
    NumToRead = 32;
    break;
  case M68kBeads::Imm3:
    NumToRead = 3;
    break;
  default:
    llvm_unreachable("invalid imm");
  }

  Scratch = (Scratch << NumToRead) | Reader.readBits(NumToRead);
}

DecodeStatus M68kDisassembler::getInstruction(MCInst &Instr, uint64_t &Size,
                            ArrayRef<uint8_t> Bytes, uint64_t Address,
                            raw_ostream &CStream) const {
  // Read and shift the input (fetch as much as we can for now).
  auto Buffer = M68kInstructionBuffer::fill(Bytes);
  if (Buffer.size() == 0) {
    return Fail;
  }

  // Check through our lookup table.
  bool Found = false;
  for (unsigned I = 0; I < Lookups.size(); ++I) {
    const M68kInstructionLookup &Lookup = Lookups[I];
    if (!Lookup.matches(Buffer)) {
      continue;
    }

    Found = true;
    Size = Lookup.size() * 2;
    Buffer.truncate(Lookup.size());
    Instr.setOpcode(Lookup.OpCode);
    LLVM_DEBUG(errs() << "decoding instruction "
                      << MCII->getName(Lookup.OpCode) << "\n");
    break;
  }

  if (!Found) {
    return Fail;
  }

  M68kInstructionReader Reader(Buffer);
  const MCInstrDesc& Desc = MCII->get(Instr.getOpcode());
  unsigned NumOperands = Desc.NumOperands;

  // Now use the beads to decode the operands.
  enum class OperandType {
    Invalid,
    Reg,
    Imm,
  };

  SmallVector<OperandType, 6> OpType(NumOperands, OperandType::Invalid);
  SmallVector<unsigned, 6> Scratch(NumOperands, 0);
  for (const uint8_t* PartPtr = M68k::getMCInstrBeads(Instr.getOpcode());
       *PartPtr; ++PartPtr) {
    uint8_t Bead = *PartPtr;
    unsigned Ext = Bead >> 4;
    unsigned Op = Bead & 0xf;
    unsigned MIOpIdx;

    switch (Op) {
    case M68kBeads::Ctrl:
      switch (Ext) {
      case M68kBeads::Ignore:
        continue;

      default:
        // Term will have already been skipped by the loop.
        llvm_unreachable("unexpected command bead");
      }

      // These bits are constant - if we're here we've already matched them.
    case M68kBeads::Bits1:
      Reader.readBits(1);
      break;
    case M68kBeads::Bits2:
      Reader.readBits(2);
      break;
    case M68kBeads::Bits3:
      Reader.readBits(3);
      break;
    case M68kBeads::Bits4:
      Reader.readBits(4);
      break;

    case M68kBeads::DAReg:
    case M68kBeads::DA:
    case M68kBeads::DReg:
    case M68kBeads::Reg:
      MIOpIdx = getRegOperandIndex(Instr, Bead);
      assert(((OpType[MIOpIdx] == OperandType::Invalid) ||
              (OpType[MIOpIdx] == OperandType::Reg)) &&
             "operands cannot change type");
      OpType[MIOpIdx] = OperandType::Reg;
      decodeReg(Instr, Bead, Reader, Scratch[MIOpIdx]);
      break;

    case M68kBeads::Disp8:
    case M68kBeads::Imm8:
    case M68kBeads::Imm16:
    case M68kBeads::Imm32:
    case M68kBeads::Imm3:
      MIOpIdx = getImmOperandIndex(Instr, Bead);
      assert(((OpType[MIOpIdx] == OperandType::Invalid) ||
             (OpType[MIOpIdx] == OperandType::Imm)) &&
             "operands cannot change type");
      OpType[MIOpIdx] = OperandType::Imm;
      decodeImm(Instr, Bead, Reader, Scratch[MIOpIdx]);
      break;

    default:
      llvm_unreachable("unhandled bead type");
    }
  }

  // Create the operands from our scratch space.
  for (unsigned O = 0; O < NumOperands; ++O) {
    switch (OpType[O]) {
    case OperandType::Invalid:
      assert(false && "operand not parsed");

    case OperandType::Imm:
      Instr.addOperand(MCOperand::createImm(Scratch[O]));
      break;

    case OperandType::Reg:
      Instr.addOperand(MCOperand::createReg(RegisterDecode[Scratch[O]]));
      break;
    }
  }

  assert((Reader.size() == 0) && "wrong number of bits consumed");
  return Success;
}

static MCDisassembler *createM68kDisassembler(const Target &T,
                                              const MCSubtargetInfo &STI,
                                              MCContext &Ctx) {
  return new M68kDisassembler(STI, Ctx, T.createMCInstrInfo());
}

extern "C" LLVM_EXTERNAL_VISIBILITY void LLVMInitializeM68kDisassembler() {
  // Register the disassembler.
  TargetRegistry::RegisterMCDisassembler(getTheM68kTarget(),
                                         createM68kDisassembler);
}
