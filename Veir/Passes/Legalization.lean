module

public import Veir.Pass
import Veir.Passes.Matching
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
public import Veir.PatternRewriter.Basic

namespace Veir

public section

inductive LegalizeAction where
| legal
| widenScalar
| custom
| unsupported
| notFound
deriving Repr, BEq

/--
  The LegalityQuery object bundles together all the information that's needed to decide whether a
  given operation is legal or not.
-/
structure LegalityQuery where
  opcode : OpCode
  bitwidths : Array Nat  /- We don't use LTT, just simple bitwidths instead. -/

def queryOf (ctx : WfIRContext OpCode) (op : OperationPtr) : Option LegalityQuery := do
  let opcode := op.getOpType! ctx.raw
  let resultTypes := op.getResultTypes! ctx.raw
  let operandTypes := op.getOperandTypes! ctx.raw
  let bitwidths ← (resultTypes ++ operandTypes).mapM (Attribute.bitwidthOfType ·.val)
  some { opcode, bitwidths := bitwidths }

/--
  The result of a query. It either indicates a final answer of Legal or Unsupported or describes an
  action that must be taken to make an operation more legal.
-/
structure LegalizeActionStep where
  action : LegalizeAction
  typeIndex : Nat := 0
  newBw : Nat := 0

abbrev LegalityPredicate := LegalityQuery → Bool
abbrev LegalizeMutation := LegalityQuery → Nat × Nat -- returns (typeIndex, newBW)

namespace LegalityPredicates

def sizeInSet (typeIndex : Nat) (sizes : Array Nat) : LegalityPredicate :=
  fun q => sizes.contains q.bitwidths[typeIndex]!

def sizeNotPow2 (typeIndex : Nat) : LegalityPredicate :=
  fun q => !Nat.isPowerOfTwo q.bitwidths[typeIndex]!

def scalarNarrowerThan (typeIndex bw : Nat) : LegalityPredicate :=
  fun q => q.bitwidths[typeIndex]! < bw

end LegalityPredicates

namespace LegalityMutations

def widenScalarToNextPow2 (typeIndex : Nat) : LegalizeMutation :=
  fun q => (typeIndex, Nat.nextPowerOfTwo q.bitwidths[typeIndex]!)

def clampScalar (typeIndex minBw maxBw : Nat) : LegalizeMutation :=
  fun q => (typeIndex, min maxBw (max minBw q.bitwidths[typeIndex]!))

end LegalityMutations

/--
  A single rule in a legalizer info ruleset.
  The specified action is chosen when the predicate is true. Where appropriate for the action
  (e.g. for WidenScalar) the new type is selected using the given mutator.
-/
structure LegalizeRule where
  predicate : LegalityPredicate
  action : LegalizeAction
  mutation : LegalizeMutation

abbrev LegalizeRuleSet := Array LegalizeRule

private def LegalizeRule.apply (rule : LegalizeRule) (q : LegalityQuery) : Option LegalizeActionStep :=
  if rule.predicate q then
    let (typeIndex, newBw) := rule.mutation q
    some { action := rule.action, typeIndex, newBw }
  else
    none

def legalFor (sizes : Array Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.sizeInSet 0 sizes
    action := .legal
    mutation := fun _ => (0, 0) }

def customFor (sizes : Array Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.sizeInSet 0 sizes
    action := .custom
    mutation := fun _ => (0, 0) }

def widenScalarToNextPow2 (typeIndex : Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.sizeNotPow2 typeIndex
    action := .widenScalar
    mutation := LegalityMutations.widenScalarToNextPow2 typeIndex }

def clampScalar (typeIndex minBw maxBw : Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.scalarNarrowerThan typeIndex maxBw
    action := .widenScalar
    mutation := LegalityMutations.clampScalar typeIndex minBw maxBw }

structure LegalizerInfo where
  ruleSets : Std.HashMap OpCode LegalizeRuleSet := ∅
  legalizeCustom : LocalRewritePattern OpCode := fun ctx _ => some (ctx, none)

namespace LegalizerInfo

def defineRuleSet
    (info : LegalizerInfo)
    (ops : Array OpCode)
    (rules : LegalizeRuleSet) : LegalizerInfo :=
  { info with
    ruleSets := ops.foldl (fun m op => m.insert op rules) info.ruleSets }

def getAction (info : LegalizerInfo) (q : LegalityQuery) : LegalizeActionStep :=
  match info.ruleSets.get? q.opcode with
  | none => { action := .notFound }
  | some ruleset =>
    (ruleset.findSome? (·.apply q)).getD { action := .notFound }

end LegalizerInfo

end

def widenScalarWPuddle (ctx : WfIRContext OpCode) (op : OperationPtr) (newBw : Nat) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  sorry

def widenScalar (ctx : WfIRContext OpCode) (op : OperationPtr) (typeGroup : Nat) (newBw : Nat) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  match op.getType! ctx.raw with
  | .gmir . add =>
    widenHomogenousBinaryOp ctx op newBw

def legalizeInstrStep (info : LegalizerInfo) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  match queryOf ctx op with
  | none => some (ctx, none)
  | some q =>
    let step := info.getAction q
    match step.action with
    | .legal => some (ctx, none)
    | .unsupported | .notFound => some (ctx, none)
    | .custom => info.legalizeCustom ctx op
    | .widenScalar => widenScalarWPuddle ctx op step.typeIndex step.newBw

end Veir
