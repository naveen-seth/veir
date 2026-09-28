module

public import Veir.GlobalOpInfo

/-!
# Legalization Rules

This file defines how a target specifies which gMIR operations it can select, and how the others
are legalized.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerInfo.h
-/

namespace Veir

public section

/-!
## Legality queries

The legality of a gMIR operation only depends on its opcode and on the type of each of its type
groups, as given by `GMIR.genericOpInfo`.
-/

/--
Low-Level-Type

For legalization, we only care about the bits a scalar occupies and not if its a float or integer.
`LLT` represents types size in bits.
TODO: make this a dedicated type once pointers or vectors are part of legalization.

Also see:
https://llvm.org/docs/GlobalISel/GMIR.html#low-level-type
-/
abbrev LLT := Nat

/-- The low-level type of `type`. Returns `none` if `type` is not an integer type. -/
def LLT.ofType? (type : TypeAttr) : Option LLT :=
  match type.val with
  | .integerType type => some type.bitwidth
  | _ => none

/-- The information from which the legality of an operation is decided. -/
structure LegalityQuery where
  /-- The opcode of the operation. -/
  opcode : GMIR
  /-- The type of each type group of the operation. -/
  types : Array LLT

/-- The legality query of `op`. Returns `none` if one of its types is not a scalar integer. -/
def LegalityQuery.of? (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR) :
    Option LegalityQuery := do
  let types ← (opcode.getTypeGroupTypes! op ctx).mapM LLT.ofType?
  return { opcode, types }

/-- The size in bits of type group `typeIdx`. -/
def LegalityQuery.sizeInBits (query : LegalityQuery) (typeIdx : Nat) : Nat :=
  query.types[typeIdx]!

/-!
## Legalization rules

A target gives a list of rules for each opcode. The legalizer takes the action of the first rule
whose predicate holds, and the operation is unsupported when no rule applies. The rule builders
follow the methods of the same name of LLVM's `LegalizeRuleSet`.
-/

/-- The action the legalizer takes on an operation. -/
inductive LegalizeAction where
  /-- The target can select the operation as is. -/
  | legal
  /-- Perform the operation with type group `typeIdx` widened to `newType`. -/
  | widenScalar (typeIdx : Nat) (newType : LLT)
  /-- The target cannot handle the operation. -/
  | unsupported

/-- A legalization rule, whose `action` is taken when `predicate` holds. -/
structure LegalizeRule where
  predicate : LegalityQuery → Bool
  action : LegalityQuery → LegalizeAction

namespace LegalizeRule

/-- The operation is legal when `predicate` holds. -/
def legalIf (predicate : LegalityQuery → Bool) : LegalizeRule :=
  { predicate, action := fun _ => .legal }

/-- The operation is legal when type group 0 is one of `types`. -/
def legalFor (types : List LLT) : LegalizeRule :=
  legalIf fun query => types.contains query.types[0]!

/-- The operation is legal when type groups 0 and 1 are one of `pairs`. -/
def legalForTypePairs (pairs : List (LLT × LLT)) : LegalizeRule :=
  legalIf fun query => pairs.contains (query.types[0]!, query.types[1]!)

/-- The operation is always legal. -/
def alwaysLegal : LegalizeRule :=
  legalIf fun _ => true

/--
The operation is widened when `predicate` holds. `mutation` gives the type group to widen and its
new type.
-/
def widenScalarIf (predicate : LegalityQuery → Bool) (mutation : LegalityQuery → Nat × LLT) :
    LegalizeRule :=
  { predicate
    action := fun query =>
      let (typeIdx, newType) := mutation query
      .widenScalar typeIdx newType }

/-- Widens type group `typeIdx` to the next power of two, and to at least `minSize` bits. -/
private def nextPow2 (typeIdx minSize : Nat) (query : LegalityQuery) : Nat × LLT :=
  (typeIdx, max (query.sizeInBits typeIdx).nextPowerOfTwo minSize)

/--
Type group `typeIdx` is widened to the next power of two, and to at least `minSize` bits, when its
size is not a power of two.
-/
def widenScalarToNextPow2 (typeIdx : Nat) (minSize : Nat := 0) : LegalizeRule :=
  widenScalarIf (fun query => !(query.sizeInBits typeIdx).isPowerOfTwo) (nextPow2 typeIdx minSize)

/--
Type group `typeIdx` is widened to the next power of two, and to at least `minSize` bits, when its
size is not a power of two or is smaller than `minSize`.
-/
def widenScalarOrEltToNextPow2OrMinSize (typeIdx minSize : Nat) : LegalizeRule :=
  widenScalarIf
    (fun query =>
      query.sizeInBits typeIdx < minSize || !(query.sizeInBits typeIdx).isPowerOfTwo)
    (nextPow2 typeIdx minSize)

/-- Type group `typeIdx` is widened to `type` when it is narrower. -/
def minScalar (typeIdx : Nat) (type : LLT) : LegalizeRule :=
  widenScalarIf (fun query => query.sizeInBits typeIdx < type) fun _ => (typeIdx, type)

end LegalizeRule

/-- The legalization rules of a target. -/
structure LegalizerInfo where
  /-- The rules of each opcode, in the order they are tried. -/
  rules : GMIR → Array LegalizeRule

/--
The action of the first rule of `opcode` whose predicate holds for `op`. Operations with non-integer
types are unsupported.
-/
def LegalizerInfo.getAction (info : LegalizerInfo) (ctx : IRContext OpCode) (op : OperationPtr)
    (opcode : GMIR) : LegalizeAction := Id.run do
  let some query := LegalityQuery.of? ctx op opcode | return .unsupported
  let some rule := (info.rules opcode).find? (·.predicate query) | return .unsupported
  return rule.action query

end

end Veir
