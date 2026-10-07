module

public import Veir.Passes.Matching.Basic
public import Veir.Passes.Legalization.LegalizerInfo

public section

/-! This file contains helper functions to match legal GMIR operations. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode GMIR]

/--
Whether a `gmir.g_add` whose type group 0 (both operands and the result) has type `type` is legal
according to the rules of `info`.
-/
def isLegalGAdd (type : TypeAttr) (info : LegalizerInfo) : Bool :=
  /- `g_add` has a single type group, so the query has a single type. -/
  (LLT.ofType? type).any fun llt =>
    info.getActionFor { opcode := .g_add, types := #[llt] } matches .legal

/-- Match a `gmir.g_add` whose types are legal. -/
def matchLegalGAdd (op : OperationPtr) (ctx : IRContext Veir.OpCode) (info : LegalizerInfo) :
    Option (ValuePtr × ValuePtr × propertiesOf GMIR.g_add) := do
  let (op', properties) ← matchOp op ctx GMIR.g_add 2
  let (lhs, rhs) := (op'[0]!, op'[1]!)
  guard (isLegalGAdd ((op.getResult 0).get! ctx).type info)
  return (lhs, rhs, properties)

end Veir
