module

public import Veir.Passes.Matching.GMIR.Basic
public import Veir.PatternRewriter.Puddle.Execution

import all Veir.Passes.Matching.GMIR.Basic
import Veir.PatternRewriter.Puddle.Validity

public section

/-! This file contains lemmas that characterize the behavior of the matching functions. -/

namespace Veir

/-- What matching a root with `matchLegalGAdd` guarantees: a `g_add` with two operands and one
    result, whose type is legal according to `info`. -/
theorem matchLegalGAdd_implies {info : LegalizerInfo} {ctx : IRContext OpCode}
    {op : OperationPtr} {assignment : Puddle.Assignment OpCode} :
    (Puddle.MatchProg.build (matchLegalGAdd info)).run ctx op = some assignment →
    op.getOpType! ctx = .gmir .g_add ∧
    (op.getOperands! ctx).size = 2 ∧
    (op.getResultTypes! ctx).size = 1 ∧
    info.isLegal .g_add #[(op.getResultTypes! ctx)[0]!] := by
  intro hmatch
  simp only [matchLegalGAdd] at hmatch
  sorry

end Veir
