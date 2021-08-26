; RUN: not llvm-mc -triple m68k -show-encoding -motorola-integers %s --show-inst-operands 2>&1 | FileCheck %s

; At the moment, all encoding tests for M68k live in llvm/test/CodeGen/M68k/.
; This is the first test included as part of the AsmMatcher and lacks encoding checks.
; The current migration plan is to consolidate all of the encoding tests in this
; directory along with AsmMatcher/ Disassembler tests like the other platforms.
; For more information and status updates see bug #49865.

.global ext_fn

; These checks have to appear first since they are printed during parsing, not
; at the end like the others. They are printed as info because the instructions
; don't (yet) support this operand format.
; CHECK: 'move.l', %6, ([50,%6],%7.4*2,20)
move.l %a0, ([50, %a0], %a1.L * 2, 20)
; CHECK: 'move.l', %6, ([50,%6,%7.4*2],20)
move.l %a0, ([50, %a0, %a1.L * 2], 20)

; CHECK: move.l %a1, %a0
move.l %a1, %a0
; CHECK: adda.l %a0, %a1
adda.l %a0, %a1
; CHECK: addx.l %d1, %d2
addx.l %d1, %d2
; CHECK: sub.w #4, %d1
sub.w #4, %d1
; CHECK: cmp.w %a0, %d0
cmp.w %a0, %d0
; CHECK: neg.w %d0
neg.w %d0
; CHECK: btst #8, %d3
btst #$8, %d3
; CHECK: bra ext_fn
bra ext_fn
; CHECK: jsr ext_fn
jsr ext_fn
; CHECK: seq %d0
seq %d0
; CHECK: sgt %d0
sgt %d0
; CHECK: lea (80,%a0), %a1
lea $50(%a0), %a1
; CHECK: lsl.l #8, %d1
lsl.l #8, %d1
; CHECK: lsr.l #8, %d1
lsr.l #8, %d1
; CHECK: asr.l #8, %d1
asr.l #8, %d1
; CHECK: rol.l #8, %d1
rol.l #8, %d1
; CHECK: ror.l #8, %d1
ror.l #8, %d1
; CHECK: nop
nop
; CHECK: rts
rts
; CHECK: movem.l %d0-%d6/%a0, (%sp)
movem.l %d0-%d6/%a0, (%sp)
; CHECK: movem.l (10,%sp), %d0-%d6/%a0
movem.l (10,%sp), %d0-%d6/%a0
; CHECK: move.l (%a0), $100
move.l (%a0), ($100).L

; TODO: the size & scale are not preserved here because they are not supported
; at codegen time (yet).
; CHECK: move.l %d0, (0,%a0,%a1)
move.l %d0, (%a0, %a1.L * 2)
