module

public import Veir.Passes.Matching.Basic
public import Veir.Passes.Legalization.LegalizerInfo

public section

/-! This file contains helper functions to match legal GMIR operations. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode GMIR]

/--
Whether a `gmir.g_add` with operand types `lhs`, `rhs` and result type `res` is legal according
to the rules of `info`.
-/
def isLegalGAdd (lhs rhs res : TypeAttr) (info : LegalizerInfo) : Bool :=
  /- `g_add` has a single type group, shared by both operands and the result. -/
  if lhs != rhs || lhs != res then false else
  match LLT.ofType? lhs with
  | none => false
  | some type =>
    let query : LegalityQuery := { opcode := .g_add, types := #[type] }
    match (info.rules .g_add).findSome? (· query) |>.getD .unsupported with
    | .legal => true
    | _ => false

/-- Match a `gmir.g_add` whose types are legal. -/
def matchLegalGAdd (op : OperationPtr) (ctx : IRContext OpCode) (info : LegalizerInfo) :
    Option (ValuePtr × ValuePtr × propertiesOf GMIR.g_add) := do
  let (op', properties) ← matchOp op ctx GMIR.g_add 2
  let (lhs, rhs) := (op'[0]!, op'[1]!)
  guard (isLegalGAdd (lhs.getType! ctx) (rhs.getType! ctx) ((op.getResult 0).get! ctx).type info)
  return (lhs, rhs, properties)

end Veir
