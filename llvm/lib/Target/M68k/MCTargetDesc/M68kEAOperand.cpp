//===-- M68kEAOperand.cpp - M68k EA Operand helpers ---------*- C++ -*-----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementation of the EA operand helpers
///
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/M68kMCTargetDesc.h"
#include "MCTargetDesc/M68kEAOperand.h"

using namespace llvm;

namespace {
enum {
  FlagsOpIndex,
  OuterRegOpIndex,
  InnerRegOpIndex,
  OuterDispOpIndex,
  InnerDispOpIndex,
  NumSubOps,
};
} // namespace

M68k::MCEAOperand::MCEAOperand() : Flags(0),
                                   OuterReg(M68k::A0), InnerReg(M68k::A0),
                                   OuterDisp(MCOperand::createImm(0)),
                                   InnerDisp(MCOperand::createImm(0))
{}

void M68k::MCEAOperand::setMode(M68k::EAOperandMode Mode) {
  Flags = (Flags &~ ModeMask) | (((uint64_t)Mode) & ModeMask);
}

M68k::MCEAOperand M68k::MCEAOperand::createAddress(MCOperand Address) {
  MCEAOperand Ret;
  Ret.setMode(EAOperandMode::Address);
  Ret.OuterDisp = Address;
  return Ret;
}

M68k::MCEAOperand M68k::MCEAOperand::createRegister(unsigned Reg) {
  MCEAOperand Ret;
  Ret.setMode(EAOperandMode::Register);
  Ret.OuterReg = Reg;
  return Ret;
}

M68k::MCEAOperand M68k::MCEAOperand::createRegPostIncrement(unsigned Reg) {
  MCEAOperand Ret;
  Ret.setMode(EAOperandMode::RegPostIncrement);
  Ret.OuterReg = Reg;
  return Ret;
}

M68k::MCEAOperand M68k::MCEAOperand::createRegPreDecrement(unsigned Reg) {
  MCEAOperand Ret;
  Ret.setMode(EAOperandMode::RegPreDecrement);
  Ret.OuterReg = Reg;
  return Ret;
}

M68k::MCEAOperand M68k::MCEAOperand::createRegisterIndirect(unsigned Reg,
                                                      MCOperand Offset) {
  MCEAOperand Ret;
  Ret.setMode(EAOperandMode::RegIndirect);
  Ret.OuterReg = Reg;
  Ret.OuterDisp = Offset.isValid() ? Offset : MCOperand::createImm(0);
  return Ret;
}

M68k::MCEAOperand M68k::MCEAOperand::createRegisterIndexed(unsigned OutReg,
                                                     MCOperand OutDisp,
                                                     unsigned InReg,
                                                     MCOperand InDisp) {
  MCEAOperand Ret;
  Ret.setMode(EAOperandMode::RegIndex);
  Ret.OuterReg = OutReg;
  Ret.OuterDisp = OutDisp;
  Ret.InnerReg = InReg;
  Ret.InnerDisp = InDisp;
  return Ret;
}

bool M68k::MCEAOperand::parseInstruction(const MCInst &MI, unsigned FirstOp) {
  assert(((FirstOp + NumSubOps) <= MI.getNumOperands()) && "insufficient operands");
  Flags = MI.getOperand(FirstOp + FlagsOpIndex).getImm();
  OuterReg = MI.getOperand(FirstOp + OuterRegOpIndex).getReg();
  InnerReg = MI.getOperand(FirstOp + InnerRegOpIndex).getReg();
  OuterDisp = MI.getOperand(FirstOp + OuterDispOpIndex);
  InnerDisp = MI.getOperand(FirstOp + InnerDispOpIndex);
  return true;
}

void M68k::MCEAOperand::addOperands(MCInst &MI) {
  MI.addOperand(MCOperand::createImm(Flags));
  MI.addOperand(MCOperand::createReg(OuterReg));
  MI.addOperand(MCOperand::createReg(InnerReg));
  MI.addOperand(OuterDisp);
  MI.addOperand(InnerDisp);
}
