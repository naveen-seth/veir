module

public import Veir.GlobalOpInfo
public import Veir.PatternRewriter.Puddle.Definitions

/-!
# Legalization Rules

This file defines how a target specifies which GMIR operations it can select, and how the others
are legalized.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerInfo.h
-/

namespace Veir

public section

/-!
## Legality queries

The legality of a gMIR operation only depends on its opcode, on the type of each of its type
groups, as given by `GMIR.genericOpInfo`, and on its immediates, as given by `GMIR.getImmediates`.
-/

/--
Low Level Type

The type's size in bits.
For legalization, we only care about the bits occupied by a *scalar*, not by floats or integers.

TODO: Make this a dedicated type once pointers or vectors are part of legalization.

Also see: https://llvm.org/docs/GlobalISel/GMIR.html#low-level-type
-/
abbrev LLT := Nat

/-- The low-level type of `type`. Returns `none` if `type` is not an integer type. -/
def LLT.ofType? (type : TypeAttr) : Option LLT :=
  match type.val with
  | .integerType type => some type.bitwidth
  | _ => none

/--
  `LegalityQuery` bundles all the information that's needed to decide whether a given operation
  is legal or not.
-/
structure LegalityQuery where
  /-- The opcode of the operation. -/
  opcode : GMIR
  /-- The type of each type group of the operation. -/
  types : Array LLT
  /-- The immediate operands of the operation. -/
  immediates : Array Int

/--
The type of each type group of an `opCode` operation with result types `resultTypes` and operand
types `operandTypes`, indexed by the type group. The type groups in `GMIR.genericOpInfo` are
expected to be numbered by the order in which they first appear.
-/
def GMIR.getTypeGroupTypes (opCode : GMIR) (resultTypes operandTypes : Array TypeAttr) :
    Array TypeAttr := Id.run do
  let mut types := #[]
  for (.type group, type) in opCode.getTypedGroups resultTypes operandTypes do
    if group == types.size then
      types := types.push type
  return types

/-- The type of each type group of `op`, indexed by the type group. -/
def GMIR.getTypeGroupTypes! (opCode : GMIR) (op : OperationPtr) (ctx : IRContext OpCode) :
    Array TypeAttr :=
  opCode.getTypeGroupTypes (op.getResultTypes! ctx) (op.getOperandTypes! ctx)

/--
The legality query of an `opcode` operation with properties `props`, result types `resultTypes`
and operand types `operandTypes`. Returns `none` if one of its types is not a scalar integer.
-/
def LegalityQuery.ofTypes? (opcode : GMIR) (props : GMIR.propertiesOf opcode)
    (resultTypes operandTypes : Array TypeAttr) : Option LegalityQuery := do
  let types ← (opcode.getTypeGroupTypes resultTypes operandTypes).mapM LLT.ofType?
  return { opcode, types, immediates := opcode.getImmediates props }

/-- The legality query of `op`. Returns `none` if one of its types is not a scalar integer. -/
def LegalityQuery.of? (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR) :
    Option LegalityQuery :=
  LegalityQuery.ofTypes? opcode (op.getProperties! ctx opcode) (op.getResultTypes! ctx) (op.getOperandTypes! ctx)

/-- The common LLT of type group `typeIdx`. -/
def LegalityQuery.getLLT! (query : LegalityQuery) (typeIdx : TypeGroup) : LLT :=
  let .type idx := typeIdx
  query.types[idx]!

/-- The immediate operand at `immIdx`. -/
def LegalityQuery.getImm! (query : LegalityQuery) (immIdx : Nat) : Int :=
  query.immediates[immIdx]!

/-!
## Legalization rules

A target gives a list of rules for each opcode. The legalizer takes the action of the first rule
that applies, and the operation is unsupported when no rule applies.
-/

/-- The action the legalizer takes on an operation. -/
inductive LegalizeAction where
  /--
  The operation is expected to be selectable directly by the target, and no transformation is
  necessary.
  -/
  | legal
  /-- The operation should be implemented with type group `typeIdx` widened to `newType`. -/
  | widenScalar (typeIdx : TypeGroup) (newType : LLT)
  /--
  The operation is legalized by the target-specific `pattern`. Unlike LLVM, where the target's
  `legalizeCustom` switches over the opcode, the rule that selects the action carries the pattern.
  -/
  | custom (pattern : Puddle.Pattern OpCode)
  /-- This operation is completely unsupported on the target. -/
  | unsupported

/-- A single legalization rule. Returns the action to take, or `none` if the rule does not apply. -/
abbrev LegalizeRule := LegalityQuery → Option LegalizeAction

namespace LegalizeRule

/-- The operation is legal if `predicate` is true. -/
def legalIf (predicate : LegalityQuery → Bool) : LegalizeRule :=
  fun query => if predicate query then some .legal else none

/-- The operation is legal when type group 0 is any type in `types`. -/
def legalFor (types : List LLT) : LegalizeRule :=
  legalIf fun query => types.contains (query.getLLT! (.type 0))

/-- The operation is legal when type groups 0 and 1 are any type pair in `pairs`. -/
def legalForTypePairs (pairs : List (LLT × LLT)) : LegalizeRule :=
  legalIf fun query => pairs.contains (query.getLLT! (.type 0), query.getLLT! (.type 1))

/-- The operation is always legal. -/
def alwaysLegal : LegalizeRule :=
  legalIf fun _ => true

/-- The operation is legalized with `pattern` if `predicate` is true. -/
def customIf (predicate : LegalityQuery → Bool) (pattern : Puddle.Pattern OpCode) : LegalizeRule :=
  fun query => if predicate query then some (.custom pattern) else none

/-- The operation is legalized with `pattern` when type group 0 is any type in `types`. -/
def customFor (types : List LLT) (pattern : Puddle.Pattern OpCode) : LegalizeRule :=
  customIf (fun query => types.contains (query.getLLT! (.type 0))) pattern

/-- Widen the scalar to the one selected by `mutation` if `predicate` is true. -/
def widenScalarIf (predicate : LegalityQuery → Bool)
    (mutation : LegalityQuery → TypeGroup × LLT) : LegalizeRule :=
  fun query => if predicate query then
    let (typeIdx, newType) := mutation query
    some (.widenScalar typeIdx newType)
  else none

/-- Ensure the scalar of type group `typeIdx` is at least as wide as `type`. -/
def minScalar (typeIdx : TypeGroup) (newType : LLT) : LegalizeRule :=
  widenScalarIf (fun query => (query.getLLT! typeIdx) < newType) fun _ => (typeIdx, newType)

end LegalizeRule

/-- The legalization rules of a target. -/
structure LegalizerInfo where
  /-- The rules of each opcode, in the order they are tried. -/
  rules : GMIR → List LegalizeRule

/--
Determine what action should be taken for `query`, using the first rule of its opcode that applies.
The operation is unsupported when no rule applies.
-/
def LegalizerInfo.getActionFor (info : LegalizerInfo) (query : LegalityQuery) : LegalizeAction :=
  (info.rules query.opcode).findSome? (· query) |>.getD .unsupported

/--
Whether an `opcode` operation with properties `props`, result types `resultTypes` and operand
types `operandTypes` is legal according to `info`. This is the legality the legalizer establishes
(see `LegalizerInfo.isLegal_of_getAction`), for use in the patterns that select legal operations.
-/
def LegalizerInfo.isLegal (info : LegalizerInfo) (opcode : GMIR) (props : GMIR.propertiesOf opcode)
    (resultTypes operandTypes : Array TypeAttr) : Bool :=
  (LegalityQuery.ofTypes? opcode props resultTypes operandTypes).any
    (info.getActionFor · matches .legal)

/--
Determine what action should be taken to legalize `op`, using the first rule of `opcode` that
applies.
-/
def LegalizerInfo.getAction (info : LegalizerInfo) (ctx : IRContext OpCode) (op : OperationPtr)
    (opcode : GMIR) : LegalizeAction := Id.run do
  let some query := LegalityQuery.of? ctx op opcode | return .unsupported
  return info.getActionFor query

/-- An operation that the legalizer leaves as legal satisfies `isLegal`. -/
theorem LegalizerInfo.isLegal_of_getAction {info : LegalizerInfo} {ctx : IRContext OpCode}
    {op : OperationPtr} {opcode : GMIR} (h : info.getAction ctx op opcode = .legal) :
    info.isLegal opcode (op.getProperties! ctx opcode) (op.getResultTypes! ctx)
      (op.getOperandTypes! ctx) := by
  grind [getAction, isLegal, LegalityQuery.of?, Option.any]

end

end Veir
