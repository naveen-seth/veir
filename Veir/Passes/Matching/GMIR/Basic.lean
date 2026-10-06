module

public import Veir.Passes.Matching.Basic
public import Veir.Passes.Legalization.LegalizerInfo

public section

/-! This file contains helper functions to match legal GMIR operations. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode GMIR]

/--
The legal types for a `gmir.g_add`, according to `riscv64LegalizerInfo`.
-/
def isLegalGAdd (lhs rhs res : TypeAttr) : Bool :=
  LLT.ofType? lhs == some 64 && LLT.ofType? rhs == some 64 && LLT.ofType? res == some 64

/-- Match a `gmir.g_add` whose types are legal. -/
def matchLegalGAdd (op : OperationPtr) (ctx : IRContext OpCode) :
    Option (ValuePtr × ValuePtr × propertiesOf GMIR.g_add) := do
  let (op', properties) ← matchOp op ctx GMIR.g_add 2
  let (lhs, rhs) := (op'[0]!, op'[1]!)
  guard (isLegalGAdd (lhs.getType! ctx) (rhs.getType! ctx) ((op.getResult 0).get! ctx).type)
  return (lhs, rhs, properties)

end Veir
