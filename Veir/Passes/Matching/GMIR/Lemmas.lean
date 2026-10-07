module

public import Veir.Passes.Matching.GMIR.Basic
public import Veir.Passes.Legalization.RISCV64LegalizerInfo

import all Veir.Passes.Matching.GMIR.Basic

public section

/-! This file contains lemmas that characterize the behavior of the matching functions. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode GMIR]

/-- What matching `gmir.g_add` (via `matchLegalGAdd`) syntactically guarantees: a `g_add` whose types
    are legal (see `isLegalGAdd`). -/
theorem matchLegalGAdd_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchLegalGAdd op ctx riscv64LegalizerInfo = some (lhs, rhs, props) →
    op.getOpType! ctx = GMIR.g_add ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx GMIR.g_add ∧
    isLegalGAdd (lhs.getType! ctx) (rhs.getType! ctx) ((op.getResult 0).get! ctx).type riscv64LegalizerInfo := by
  intro hmatch
  simp only [matchLegalGAdd, bind, Option.bind, pure, guard, failure] at hmatch
  grind

end Veir
