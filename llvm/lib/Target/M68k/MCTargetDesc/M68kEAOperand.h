//===-- M68kEAOperand.h - Helper for composite EA MC operands --*- C++ -*--===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains helpers for dealing with the multiple MC operands
/// which cover a single logical EA operand.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_M68K_MCTARGETDESC_M68KEAOPERAND_H
#define LLVM_LIB_TARGET_M68K_MCTARGETDESC_M68KEAOPERAND_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/MC/MCInst.h"

namespace llvm {

namespace M68k {

enum class EAOperandMode {
  Address,
  Register,
  RegIndirect,
  RegPostIncrement,
  RegPreDecrement,
  RegIndex,
};

struct MCEAOperand {
  uint64_t Flags;
  unsigned OuterReg;
  unsigned InnerReg;
  MCOperand OuterDisp;
  MCOperand InnerDisp;

  enum {
    ModeBits = 3,
    ModeMask = (1 << ModeBits) - 1,
  };

  MCEAOperand();

  inline EAOperandMode getMode() const {
    return (EAOperandMode)(Flags & ModeMask);
  }

  void setMode(EAOperandMode Mode);

  static MCEAOperand createAddress(MCOperand Address);
  static MCEAOperand createRegister(unsigned Reg);
  static MCEAOperand createRegPostIncrement(unsigned Reg);
  static MCEAOperand createRegPreDecrement(unsigned Reg);
  static MCEAOperand createRegisterIndirect(unsigned Reg,
                                            MCOperand Offset = MCOperand());
  static MCEAOperand createRegisterIndexed(unsigned OuterReg,
                                           MCOperand OuterDisp,
                                           unsigned InnerReg,
                                           MCOperand InnerDisp);

  bool parseInstruction(const MCInst &MI, unsigned FirstOp);
  void addOperands(MCInst &MI);
};

} // namespace M68k

} // namespace llvm

#endif
