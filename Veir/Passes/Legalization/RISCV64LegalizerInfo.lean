module

public import Veir.Pass
public import Veir.Passes.Legalization.LegalizerInfo
import Veir.Passes.Legalization.Legalizer
import Veir.Passes.Legalization.LegalizerHelper
import Veir.PatternRewriter.Puddle.Builders

/-!
# RISC-V 64 Legalization

This file implements the legalization pass for RISC-V 64.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp
-/

namespace Veir

open Puddle in
/--
Computes an `i32` binary `opcode` operation on `i64` and sign-extends the result from bit 31, so
that instruction selection can pick the word instruction (`addw`, `subw`). This is the custom
legalization of `G_ADD` and `G_SUB` in LLVM's `RISCVLegalizerInfo`, and is called
`customLegalizeToWOpWithSExt` in LLVM's `RISCVISelLowering`.
-/
def customLegalizeToWOpWithSExt (opcode : GMIR) (noFlags : propertiesOf (OpCode.gmir opcode)) :
    Pattern OpCode :=
  Pattern.Builder (matchBinop opcode)
    (fun (type, lhs, rhs) => do
      let wideType ← CreateProg.type (IntegerType.signless 64)
      let wideLhs ← widenScalarSrc .g_anyext () wideType lhs
      let wideRhs ← widenScalarSrc .g_anyext () wideType rhs
      let props ← CreateProg.property (.gmir opcode) noFlags
      let wide ← CreateProg.operation (.gmir opcode) #[wideLhs, wideRhs] #[wideType] props
      let sextProps ← CreateProg.property (.gmir .g_sext_inreg) ⟨32⟩
      let sext ← CreateProg.operation (.gmir .g_sext_inreg) #[wide.res[0]!] #[wideType] sextProps
      widenScalarDst sext.res[0]! type)
    (fun trunc => trunc)

public section

def riscv64LegalizerInfo : LegalizerInfo where
  rules
    | .g_add => [
      .legalFor [64],
      .customFor [32] (customLegalizeToWOpWithSExt .g_add ⟨false, false⟩),
      .minScalar (.type 0) 64,
    ]
    | .g_sub => [
      .legalFor [64],
      .customFor [32] (customLegalizeToWOpWithSExt .g_sub ⟨false, false⟩),
      .minScalar (.type 0) 64,
    ]
    | .g_icmp => [
      .legalForTypePairs [(64, 64)],
      .minScalar (.type 1) 64,
      .minScalar (.type 0) 64,
    ]
    | .g_anyext => [
      .alwaysLegal,
    ]
    | .g_sext | .g_zext => [
      -- In LLVM, extensions from other widths never reach these rules: their operands are always
      -- the result of a  `g_trunc`, and the artifact combiner turns them into `g_sext_inreg`
      -- or `g_and`.
      -- FIXME: Add `g_sext_inreg`, `g_and` and these folds. Until then, other widths always legal.
      .legalForTypePairs [(32, 16), (64, 16), (64, 32)],
      .alwaysLegal
    ]
    | .g_trunc => [
      .alwaysLegal,
    ]
    | .g_sext_inreg => [
      -- `sz` 8 and 16 need Zbb, which VeIR assumes since it selects `sext.b` and `sext.h`.
      .legalIf fun query => query.getLLT! (.type 0) == 64 && [8, 16, 32].contains (query.getImm! 0),
    ]

def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize gMIR operations for RISC-V 64."
    run := fun _ ctx _ _ => riscv64LegalizerInfo.legalize ctx }

end

end Veir
