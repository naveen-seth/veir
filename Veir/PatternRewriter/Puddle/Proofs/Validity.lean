module

public import Veir.PatternRewriter.Puddle.Validity

import Veir.Data.Refinement
import all Veir.GlobalOpInfo
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.Basic
import all Veir.Interpreter.EquationLemma
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics
import all Veir.Verifier.Lemmas
import Lean.Elab.Tactic.Unfold

/-! Proof support and tactics for author-facing Puddle validity obligations. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
The interpreter's side-effect table is the trusted bridge between an operation being marked as
effect-free and the memory-independence property used by the equation lemma.
-/
axiom OperationPtr.Pure.of_getEffects_eq_none
    {op : OperationPtr} {ctx : IRContext OpCode}
    (h : HasOpInfo.getEffects (op.getOpType! ctx)
      (op.getProperties! ctx (op.getOpType! ctx)) == .none) :
    op.Pure ctx

/-- Non-terminating opcodes never produce a control-flow action. -/
axiom controlFlow_eq_none_of_isTerminator_eq_false
    {opCode : OpCode} {actual : propertiesOf opCode}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {successors : Array BlockPtr} {memory memory' : MemoryState}
    {results : Array RuntimeValue} {controlFlow : Option ControlFlowAction}
    (hterminator : HasOpInfo.isTerminator opCode = false)
    (hinterpret : interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory', controlFlow)) :
    controlFlow = none

/-- Successful dialect interpretation returns values conforming to the declared result types. -/
axiom interpretOp'_results_conform_of_eq_some
    {opCode : OpCode} {actual : propertiesOf opCode}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue}
    {successors : Array BlockPtr} {memory memory' : MemoryState}
    {results : Array RuntimeValue} {controlFlow : Option ControlFlowAction}
    (hinterpret : interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory', controlFlow)) :
    RuntimeValue.ArrayConforms results resultTypes

theorem PropertyMatcher.Supported.pure
    {opCode : OpCode} {property : PropertyMatcher opCode}
    {numOperands numResults : Nat}
    {op : OperationPtr} {ctx : IRContext OpCode}
    (hsupported : property.Supported numOperands numResults)
    (hOpCode : op.getOpType! ctx = opCode)
    (hproperty : property (op.getProperties! ctx opCode) = true) :
    op.Pure ctx := by
  apply OperationPtr.Pure.of_getEffects_eq_none
  subst opCode
  exact hsupported.2 _ hproperty

@[simp]
theorem SemanticCreateAssignment.getType_bindOp_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op)
    (query : Handle OpCode .type) (results : Array RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getType query = assignment.getType query := by
  simp only [SemanticCreateAssignment.bindOp]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticCreateAssignment.getType_bindValue_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .value)
    (query : Handle OpCode .type) (value : RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getType query = assignment.getType query := by
  simp only [SemanticCreateAssignment.bindValue]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticAssignment.getType_bindCreatedOp_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op)
    (query : Handle OpCode .type) (results : Array RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getType (SemanticCreateAssignment.bindOp assignment bound results) query =
      SemanticAssignment.getType assignment query := by
  exact SemanticCreateAssignment.getType_bindOp_of_ne assignment bound query results hneq

@[simp]
theorem SemanticAssignment.getType_bindCreatedValue_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .value)
    (query : Handle OpCode .type) (value : RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getType (SemanticCreateAssignment.bindValue assignment bound value) query =
      SemanticAssignment.getType assignment query := by
  exact SemanticCreateAssignment.getType_bindValue_of_ne assignment bound query value hneq

/-! Keep native metadata evaluation at the public assignment API during validity simplification. -/

@[simp]
theorem MetadataStore.getType_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) :
    MetadataStore.getType assignment handle = assignment.getType handle := by
  rfl

@[simp]
theorem MetadataStore.getProperty_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) :
    MetadataStore.getProperty assignment handle = assignment.getProperty handle := by
  rfl

@[simp]
theorem MetadataStore.bindType_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) (value : TypeAttr) :
    MetadataStore.bindType assignment handle value =
      some (assignment.bindType handle value) := by
  rfl

@[simp]
theorem MetadataStore.bindProperty_semantic (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) :
    MetadataStore.bindProperty assignment handle value =
      some (assignment.bindProperty handle value) := by
  rfl

theorem SemanticCreateAssignment.getValue_bindValue_of_eq
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bindValue bound value).getValue query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq
  subst query
  simp only [SemanticCreateAssignment.bindValue]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    simp [SemanticCreateAssignment.getValue, h]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    simp only [SemanticCreateAssignment.getValue, Array.getElem?_append]
    simp [hs]

theorem SemanticCreateAssignment.getValue_bindValue_of_ne
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindValue]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

theorem SemanticCreateAssignment.getValue_bindOp_of_eq
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (heq : query.id = bound.id) :
    (assignment.bindOp bound results).getValue query = none := by
  simp only [SemanticCreateAssignment.bindOp]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set]
    simp [heq]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    unfold SemanticCreateAssignment.getValue
    simp only [Array.getElem?_append]
    simp [hs, heq]

theorem SemanticCreateAssignment.getValue_bindOp_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindOp]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

theorem SemanticCreateAssignment.getValue_bindProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getValue query = assignment.getValue query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getValue
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getValue
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticCreateAssignment.getOp_bindProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .op) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getOp query = assignment.getOp query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getOp
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getOp
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticCreateAssignment.getType_bindProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getType query = assignment.getType query := by
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rename_i h
    have hs : assignment.size ≤ bound.id := Nat.le_of_not_gt h
    have hsize : assignment.size + (bound.id - assignment.size) = bound.id :=
      Nat.add_sub_of_le hs
    unfold SemanticCreateAssignment.getType SemanticAssignment.getType
    simp only [Array.size_append, Array.size_replicate,
      Array.getElem?_append, Array.getElem?_replicate]
    rw [hsize]
    by_cases hquery : query.id < assignment.size
    · have hqb : query.id < bound.id := Nat.lt_of_lt_of_le hquery hs
      simp [hquery, hqb]
    · have hqs : assignment.size ≤ query.id := Nat.le_of_not_gt hquery
      by_cases hqb : query.id < bound.id
      · have hgap : query.id - assignment.size < bound.id - assignment.size :=
          Nat.sub_lt_sub_right hqs hqb
        simp [hquery, hqb, hgap]
      · have hbq : bound.id < query.id := by omega
        have hdiff : query.id - bound.id ≠ 0 := by omega
        simp [hquery, hqb, hdiff]

@[simp]
theorem SemanticAssignment.getType_bindCreatedProperty_of_ne
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getType
        (SemanticCreateAssignment.bindProperty assignment bound value) query =
      SemanticAssignment.getType assignment query := by
  exact SemanticCreateAssignment.getType_bindProperty_of_ne
    assignment bound query value hneq

theorem SemanticCreateAssignment.getProperty_bindProperty_of_eq
    (assignment : SemanticCreateAssignment) (bound query : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) (heq : query.id = bound.id) :
    (assignment.bindProperty bound value).getProperty query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq
  subst query
  simp only [SemanticCreateAssignment.bindProperty]
  unfold SemanticCreateAssignment.bind
  split
  · rename_i h
    simp [SemanticCreateAssignment.getProperty, SemanticAssignment.getProperty, h]
  · rename_i h
    have hs : assignment.size ≤ bound := Nat.le_of_not_gt h
    simp only [SemanticCreateAssignment.getProperty, SemanticAssignment.getProperty,
      Array.getElem?_append]
    simp [hs]

@[simp]
theorem SemanticCreateAssignment.getProperty_bindProperty_self
    (assignment : SemanticCreateAssignment) (bound : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bindProperty bound value).getProperty bound = some value := by
  exact SemanticCreateAssignment.getProperty_bindProperty_of_eq
    assignment bound bound value rfl

theorem SemanticAssignment.getElem?_bind_of_ne
    (assignment : SemanticAssignment) (bound query : Nat)
    (binding : SemanticBinding) (hneq : query ≠ bound) :
    (assignment.bind bound binding)[query]? = assignment[query]? := by
  unfold SemanticAssignment.bind Array.setIfInBounds
  split
  · rename_i h
    rw [Array.getElem?_set_ne h (Ne.symm hneq)]
  · rfl

theorem SemanticAssignment.getElem?_bind_of_eq
    (assignment : SemanticAssignment) (id : Nat)
    (binding : SemanticBinding) (hbound : id < assignment.size) :
    (assignment.bind id binding)[id]? = some (some binding) := by
  unfold SemanticAssignment.bind Array.setIfInBounds
  simp [hbound]

@[simp] theorem SemanticAssignment.size_bind
    (assignment : SemanticAssignment) (id : Nat) (binding : SemanticBinding) :
    (assignment.bind id binding).size = assignment.size := by
  unfold SemanticAssignment.bind Array.setIfInBounds
  split <;> simp_all

@[simp] theorem SemanticAssignment.size_bindOp
    (assignment : SemanticAssignment) (handle : Handle OpCode .op) (results : Array RuntimeValue) :
    (assignment.bindOp handle results).size = assignment.size := by
  simp [SemanticAssignment.bindOp]

@[simp] theorem SemanticAssignment.size_bindValue
    (assignment : SemanticAssignment) (handle : Handle OpCode .value) (value : RuntimeValue) :
    (assignment.bindValue handle value).size = assignment.size := by
  simp [SemanticAssignment.bindValue]

@[simp] theorem SemanticAssignment.size_bindType
    (assignment : SemanticAssignment) (handle : Handle OpCode .type) (value : TypeAttr) :
    (assignment.bindType handle value).size = assignment.size := by
  simp [SemanticAssignment.bindType]

@[simp] theorem SemanticAssignment.size_bindProperty
    (assignment : SemanticAssignment) (handle : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    (assignment.bindProperty handle value).size = assignment.size := by
  simp [SemanticAssignment.bindProperty]

@[simp] theorem SemanticAssignment.getValue_bindMatchedValue_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindValue bound value).getValue query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindValue SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_eq assignment bound _ hbound]

@[simp] theorem SemanticAssignment.getValue_bindMatchedValue_of_ne
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindValue SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getOp_bindMatchedValue_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .value) (query : Handle OpCode .op)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getOp query = assignment.getOp query := by
  unfold SemanticAssignment.bindValue SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getProperty_bindMatchedValue_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .value)
    (query : Handle OpCode (.prop opCode)) (value : RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getProperty query = assignment.getProperty query := by
  unfold SemanticAssignment.bindValue SemanticAssignment.getProperty
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getValue_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getValue_bindMatchedType_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .type) (query : Handle OpCode .value)
    (value : TypeAttr) (hneq : query.id ≠ bound.id) :
    (assignment.bindType bound value).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindType SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getType_bindMatchedType_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .type)
    (value : TypeAttr) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindType bound value).getType query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindType SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_eq assignment bound _ hbound]

@[simp] theorem SemanticAssignment.getType_bindMatchedValue_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .value) (query : Handle OpCode .type)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindValue bound value).getType query = assignment.getType query := by
  unfold SemanticAssignment.bindValue SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getOp_bindMatchedType_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .type) (query : Handle OpCode .op)
    (value : TypeAttr) (hneq : query.id ≠ bound.id) :
    (assignment.bindType bound value).getOp query = assignment.getOp query := by
  unfold SemanticAssignment.bindType SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getType_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .type)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getType query = assignment.getType query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getOp_bindMatchedOp_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .op)
    (results : Array RuntimeValue) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindOp bound results).getOp query = some results := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindOp SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_eq assignment bound _ hbound]

@[simp] theorem SemanticAssignment.getOp_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound query : Handle OpCode .op)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getOp query = assignment.getOp query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp] theorem SemanticAssignment.getProperty_bindMatchedOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op)
    (query : Handle OpCode (.prop opCode)) (results : Array RuntimeValue)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindOp bound results).getProperty query = assignment.getProperty query := by
  unfold SemanticAssignment.bindOp SemanticAssignment.getProperty
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getValue_bindMatchedProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getValue query = assignment.getValue query := by
  unfold SemanticAssignment.bindProperty SemanticAssignment.getValue
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getOp_bindMatchedProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .op) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getOp query = assignment.getOp query := by
  unfold SemanticAssignment.bindProperty SemanticAssignment.getOp
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getType_bindMatchedProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .type) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    (assignment.bindProperty bound value).getType query = assignment.getType query := by
  unfold SemanticAssignment.bindProperty SemanticAssignment.getType
  rw [SemanticAssignment.getElem?_bind_of_ne assignment bound.id query.id _ hneq]

@[simp]
theorem SemanticAssignment.getProperty_bindMatchedProperty_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) (heq : query.id = bound.id)
    (hbound : bound.id < assignment.size) :
    (assignment.bindProperty bound value).getProperty query = some value := by
  rcases bound with ⟨bound⟩
  rcases query with ⟨query⟩
  simp only at heq hbound ⊢
  subst query
  unfold SemanticAssignment.bindProperty SemanticAssignment.bind
  simp [SemanticAssignment.getProperty, Array.setIfInBounds, hbound]

/-!
`CreateDecl` is phrased in terms of `SemanticAssignment`, while the update lemmas above use the
creation-assignment API.  Keep these forwarding equations opaque and high-level so simplification
never expands the backing array representation.
-/

@[simp]
theorem SemanticAssignment.getValue_bindValue_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (heq : query.id = bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindValue assignment bound value) query =
      some value := by
  exact SemanticCreateAssignment.getValue_bindValue_of_eq assignment bound query value heq

@[simp]
theorem SemanticAssignment.getValue_bindValue_of_ne
    (assignment : SemanticAssignment) (bound query : Handle OpCode .value)
    (value : RuntimeValue) (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindValue assignment bound value) query =
      SemanticAssignment.getValue assignment query := by
  exact SemanticCreateAssignment.getValue_bindValue_of_ne assignment bound query value hneq

@[simp]
theorem SemanticAssignment.getValue_bindOp_of_eq
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (heq : query.id = bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindOp assignment bound results) query =
      none := by
  exact SemanticCreateAssignment.getValue_bindOp_of_eq assignment bound query results heq

@[simp]
theorem SemanticAssignment.getValue_bindOp_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode .op) (query : Handle OpCode .value)
    (results : Array RuntimeValue) (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindOp assignment bound results) query =
      SemanticAssignment.getValue assignment query := by
  exact SemanticCreateAssignment.getValue_bindOp_of_ne assignment bound query results hneq

@[simp]
theorem SemanticAssignment.getValue_bindProperty_of_ne
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (query : Handle OpCode .value) (value : propertiesOf opCode)
    (hneq : query.id ≠ bound.id) :
    SemanticAssignment.getValue (SemanticCreateAssignment.bindProperty assignment bound value) query =
      SemanticAssignment.getValue assignment query := by
  exact SemanticCreateAssignment.getValue_bindProperty_of_ne assignment bound query value hneq

@[simp]
theorem SemanticAssignment.getProperty_bindProperty_of_eq
    (assignment : SemanticAssignment) (bound query : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) (heq : query.id = bound.id) :
    SemanticAssignment.getProperty
        (SemanticCreateAssignment.bindProperty assignment bound value) query = some value := by
  exact SemanticCreateAssignment.getProperty_bindProperty_of_eq assignment bound query value heq

@[simp]
theorem SemanticAssignment.getProperty_bindProperty_self
    (assignment : SemanticAssignment) (bound : Handle OpCode (.prop opCode))
    (value : propertiesOf opCode) :
    SemanticAssignment.getProperty
        (SemanticCreateAssignment.bindProperty assignment bound value) bound = some value := by
  exact SemanticCreateAssignment.getProperty_bindProperty_self assignment bound value
private theorem Array.exists_eq_singleton_of_size_eq_one {values : Array α}
    (hsize : values.size = 1) : ∃ value, values = #[value] := by
  rcases values with ⟨values⟩
  simp only [List.size_toArray] at hsize
  match values, hsize with
  | [value], _ => exact ⟨value, rfl⟩

/-- A successful single-integer-result interpretation exposes exactly one typed value.

This is the normalization that lets `puddle_simp` erase the array and assignment machinery
before presenting an operation's semantic obligation to a pattern author. -/
theorem PropertyMatcher.Interprets.exists_integer_result
    (hinterpret : PropertyMatcher.Interprets opCode actual
      #[(IntegerType.mk bitwidth : TypeAttr)] operands results) :
    ∃ result : Data.LLVM.Int bitwidth, results = #[.int bitwidth result] := by
  rcases hinterpret with ⟨successors, memory, controlFlow, hinterpret⟩
  have hconforms := interpretOp'_results_conform_of_eq_some hinterpret
  have hsize : results.size = 1 := by
    simpa [RuntimeValue.ArrayConforms] using hconforms.1
  rcases Array.exists_eq_singleton_of_size_eq_one hsize with ⟨result, rfl⟩
  have hresult := hconforms.2 0 (by simp)
  simp at hresult
  rcases RuntimeValue.Conforms.integerType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

/-- A successful single-result interpretation exposes one value conforming to its result type. -/
private theorem PropertyMatcher.Interprets.exists_conforming_single_result
    (hinterpret : PropertyMatcher.Interprets opCode actual #[resultType] operands results) :
    ∃ result, results = #[result] ∧ RuntimeValue.Conforms result resultType := by
  rcases hinterpret with ⟨successors, memory, controlFlow, hinterpret⟩
  have hconforms := interpretOp'_results_conform_of_eq_some hinterpret
  have hsize : results.size = 1 := by
    simpa [RuntimeValue.ArrayConforms] using hconforms.1
  rcases Array.exists_eq_singleton_of_size_eq_one hsize with ⟨result, rfl⟩
  exact ⟨result, rfl, hconforms.2 0 (by simp)⟩

theorem PropertyMatcher.Interprets.exists_float_result
    (hinterpret : PropertyMatcher.Interprets opCode actual
      #[(FloatType.mk bitwidth : TypeAttr)] operands results) :
    ∃ result : Float, results = #[.float bitwidth result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.floatType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_byte_result
    (hinterpret : PropertyMatcher.Interprets opCode actual
      #[(LLVM.ByteType.mk bitwidth : TypeAttr)] operands results) :
    ∃ result : Data.LLVM.Byte bitwidth, results = #[.byte bitwidth result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.byteType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_modArith_result
    {type : ModArithType}
    (hinterpret : PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands results) :
    ∃ result : Data.LLVM.Int type.modulus.type.bitwidth,
      results = #[.int type.modulus.type.bitwidth result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.modArithType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_register_result
    {type : RegisterType}
    (hinterpret : PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands results) :
    ∃ result : Data.RISCV.Reg, results = #[.reg result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.registerType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

theorem PropertyMatcher.Interprets.exists_pointer_result
    {type : LLVM.PointerType}
    (hinterpret : PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands results) :
    ∃ result : UInt64, results = #[.addr result] := by
  rcases hinterpret.exists_conforming_single_result with ⟨result, rfl, hresult⟩
  rcases RuntimeValue.Conforms.llvmPointerType hresult with ⟨result, rfl⟩
  exact ⟨result, rfl⟩

/-- Author-facing form of a property denotation for Puddle's single integer result. -/
theorem PropertyMatcher.denote_single_integer
    (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(IntegerType.mk bitwidth : TypeAttr)] operands next ↔
      ∀ actual, property actual = true →
        ∀ result : Data.LLVM.Int bitwidth,
          PropertyMatcher.Interprets opCode actual
            #[(IntegerType.mk bitwidth : TypeAttr)] operands #[.int bitwidth result] →
          next actual #[.int bitwidth result] := by
  constructor
  · intro hdenote actual hproperty result hinterpret
    exact hdenote actual hproperty _ hinterpret
  · intro hdenote actual hproperty results hinterpret
    rcases hinterpret.exists_integer_result with ⟨result, rfl⟩
    exact hdenote actual hproperty result hinterpret

theorem PropertyMatcher.denote_single_float
    (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(FloatType.mk bitwidth : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : Float,
        PropertyMatcher.Interprets opCode actual #[(FloatType.mk bitwidth : TypeAttr)] operands
          #[.float bitwidth result] → next actual #[.float bitwidth result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_float_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_byte
    (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(LLVM.ByteType.mk bitwidth : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : Data.LLVM.Byte bitwidth,
        PropertyMatcher.Interprets opCode actual #[(LLVM.ByteType.mk bitwidth : TypeAttr)] operands
          #[.byte bitwidth result] → next actual #[.byte bitwidth result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_byte_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_modArith
    {type : ModArithType} (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(type : TypeAttr)] operands next ↔
      ∀ actual, property actual = true →
        ∀ result : Data.LLVM.Int type.modulus.type.bitwidth,
          PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands
            #[.int type.modulus.type.bitwidth result] →
          next actual #[.int type.modulus.type.bitwidth result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_modArith_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_register
    {type : RegisterType} (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(type : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : Data.RISCV.Reg,
        PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands #[.reg result] →
          next actual #[.reg result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_register_result with ⟨result, rfl⟩
    exact h actual hp result hi

theorem PropertyMatcher.denote_single_pointer
    {type : LLVM.PointerType} (property : PropertyMatcher opCode) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) :
    property.denote #[(type : TypeAttr)] operands next ↔
      ∀ actual, property actual = true → ∀ result : UInt64,
        PropertyMatcher.Interprets opCode actual #[(type : TypeAttr)] operands #[.addr result] →
          next actual #[.addr result] := by
  constructor
  · intro h actual hp result hi; exact h actual hp _ hi
  · intro h actual hp results hi
    rcases hi.exists_pointer_result with ⟨result, rfl⟩
    exact h actual hp result hi


theorem TypeMatcher.denote_type {Attr : Type} [IsTypeAttr Attr]
    (matcher : Attr → Bool) (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? Attr).map matcher).getD false) next ↔
      ∀ specificAttr : Attr, matcher specificAttr = true →
        next (specificAttr : TypeAttr) := by
  unfold TypeMatcher.denote
  constructor
  · intro h specificAttr hmatcher
    apply h (specificAttr : TypeAttr)
    have hcast : ((specificAttr : TypeAttr).cast? Attr) = some specificAttr := by
      change (TypeAttr.of Attr specificAttr).cast? Attr = some specificAttr
      exact IsTypeAttr.cast?_of specificAttr
    simp [hcast, hmatcher]
  · intro h attr hmatcher
    cases hcast : attr.cast? Attr with
    | none => simp [hcast] at hmatcher
    | some specificAttr =>
      simp [hcast] at hmatcher
      have heq : (specificAttr : TypeAttr) = attr := by
        change TypeAttr.of Attr specificAttr = attr
        exact (IsTypeAttr.cast?_eq_some_iff attr specificAttr).mp hcast
      rw [← heq]
      exact h specificAttr hmatcher

/-- Pointwise counterpart of `TypeMatcher.denote_type`, used to unpack a matcher model into the
specific type accepted by a typed Puddle matcher. -/
@[simp 2000]
theorem TypeMatcher.accepts_type {Attr : Type} [IsTypeAttr Attr]
    (matcher : Attr → Bool) (type : TypeAttr) :
    ((type.cast? Attr).map matcher).getD false = true ↔
      ∃ specificAttr : Attr, type = (specificAttr : TypeAttr) ∧ matcher specificAttr = true := by
  constructor
  · intro h
    cases hcast : type.cast? Attr with
    | none => simp [hcast] at h
    | some specificAttr =>
      have heq : (specificAttr : TypeAttr) = type :=
        (IsTypeAttr.cast?_eq_some_iff type specificAttr).mp hcast
      exact ⟨specificAttr, heq.symm, by simpa [hcast] using h⟩
  · rintro ⟨specificAttr, rfl, hmatcher⟩
    have hcast : ((specificAttr : TypeAttr).cast? Attr) = some specificAttr := by
      exact IsTypeAttr.cast?_of specificAttr
    simp [hcast, hmatcher]

/-! These specialized forms expose the canonical `TypeAttr` constructor. That matters to
`RuntimeValue.Conforms`: a generic `IsTypeAttr` coercion is intentionally abstract, while a closed
Puddle rule uses one of these canonical instances. -/

@[simp 3000]
theorem TypeMatcher.accepts_integerType (matcher : IntegerType → Bool) (type : TypeAttr) :
    ((type.cast? IntegerType).map matcher).getD false = true ↔
      ∃ intType, type = Attribute.asType (.integerType intType) ∧ matcher intType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrIntegerType] using
    (@TypeMatcher.accepts_type IntegerType instIsTypeAttrIntegerType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_floatType (matcher : FloatType → Bool) (type : TypeAttr) :
    ((type.cast? FloatType).map matcher).getD false = true ↔
      ∃ floatType, type = Attribute.asType (.floatType floatType) ∧ matcher floatType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrFloatType] using
    (@TypeMatcher.accepts_type FloatType instIsTypeAttrFloatType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_byteType (matcher : LLVM.ByteType → Bool) (type : TypeAttr) :
    ((type.cast? LLVM.ByteType).map matcher).getD false = true ↔
      ∃ byteType, type = Attribute.asType (.byteType byteType) ∧ matcher byteType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrByteType] using
    (@TypeMatcher.accepts_type LLVM.ByteType instIsTypeAttrByteType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_modArithType (matcher : ModArithType → Bool) (type : TypeAttr) :
    ((type.cast? ModArithType).map matcher).getD false = true ↔
      ∃ modType, type = Attribute.asType (.modArithType modType) ∧ matcher modType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrModArithType] using
    (@TypeMatcher.accepts_type ModArithType instIsTypeAttrModArithType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_registerType (matcher : RegisterType → Bool) (type : TypeAttr) :
    ((type.cast? RegisterType).map matcher).getD false = true ↔
      ∃ registerType, type = Attribute.asType (.registerType registerType) ∧
        matcher registerType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrRegisterType] using
    (@TypeMatcher.accepts_type RegisterType instIsTypeAttrRegisterType matcher type)

@[simp 3000]
theorem TypeMatcher.accepts_pointerType (matcher : LLVM.PointerType → Bool) (type : TypeAttr) :
    ((type.cast? LLVM.PointerType).map matcher).getD false = true ↔
      ∃ pointerType, type = Attribute.asType (.llvmPointerType pointerType) ∧
        matcher pointerType = true := by
  simpa only [Coe.coe, IsTypeAttr.toCoe, instIsTypeAttrPointerType] using
    (@TypeMatcher.accepts_type LLVM.PointerType instIsTypeAttrPointerType matcher type)

/-! Pointwise conformance equations turn model witnesses back into the typed runtime values exposed
by the author-facing validity obligation. -/

@[simp 2000]
theorem RuntimeValue.conforms_integerType_iff (runtimeValue : RuntimeValue)
    (intType : IntegerType) :
    runtimeValue.Conforms (intType : TypeAttr) ↔
      ∃ value, runtimeValue = .int intType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.integerType
  · rintro ⟨value, rfl⟩
    change intType.bitwidth = intType.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_floatType_iff (runtimeValue : RuntimeValue)
    (floatType : FloatType) :
    runtimeValue.Conforms (floatType : TypeAttr) ↔
      ∃ value, runtimeValue = .float floatType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.floatType
  · rintro ⟨value, rfl⟩
    change floatType.bitwidth = floatType.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_byteType_iff (runtimeValue : RuntimeValue)
    (byteType : LLVM.ByteType) :
    runtimeValue.Conforms (byteType : TypeAttr) ↔
      ∃ value, runtimeValue = .byte byteType.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.byteType
  · rintro ⟨value, rfl⟩
    change byteType.bitwidth = byteType.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_modArithType_iff (runtimeValue : RuntimeValue)
    (modType : ModArithType) :
    runtimeValue.Conforms (modType : TypeAttr) ↔
      ∃ value, runtimeValue = .int modType.modulus.type.bitwidth value := by
  constructor
  · exact RuntimeValue.Conforms.modArithType
  · rintro ⟨value, rfl⟩
    change modType.modulus.type.bitwidth = modType.modulus.type.bitwidth
    rfl

@[simp 2000]
theorem RuntimeValue.conforms_registerType_iff (runtimeValue : RuntimeValue)
    (registerType : RegisterType) :
    runtimeValue.Conforms (registerType : TypeAttr) ↔
      ∃ value, runtimeValue = .reg value := by
  constructor
  · exact RuntimeValue.Conforms.registerType
  · rintro ⟨value, rfl⟩
    change True
    trivial

@[simp 2000]
theorem RuntimeValue.conforms_pointerType_iff (runtimeValue : RuntimeValue)
    (pointerType : LLVM.PointerType) :
    runtimeValue.Conforms (pointerType : TypeAttr) ↔
      ∃ value, runtimeValue = .addr value := by
  constructor
  · exact RuntimeValue.Conforms.llvmPointerType
  · rintro ⟨value, rfl⟩
    change True
    trivial

@[simp 2000]
theorem TypeMatcher.denote_integer (matcher : IntegerType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? IntegerType).map matcher).getD false) next ↔
      ∀ bitwidth, matcher (IntegerType.mk bitwidth) = true →
        next (IntegerType.mk bitwidth : TypeAttr) := by
  rw [TypeMatcher.denote_type]
  constructor
  · intro h bitwidth hmatcher
    exact h (IntegerType.mk bitwidth) hmatcher
  · intro h type hmatcher
    rcases type with ⟨bitwidth⟩
    exact h bitwidth hmatcher

@[simp 2000]
theorem TypeMatcher.denote_float (matcher : FloatType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? FloatType).map matcher).getD false) next ↔
      ∀ bitwidth, matcher (FloatType.mk bitwidth) = true →
        next (FloatType.mk bitwidth : TypeAttr) := by
  rw [TypeMatcher.denote_type]
  constructor
  · intro h bitwidth hmatcher
    exact h (FloatType.mk bitwidth) hmatcher
  · intro h type hmatcher
    rcases type with ⟨bitwidth⟩
    exact h bitwidth hmatcher

@[simp 2000]
theorem TypeMatcher.denote_byte (matcher : LLVM.ByteType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? LLVM.ByteType).map matcher).getD false) next ↔
      ∀ bitwidth, matcher (LLVM.ByteType.mk bitwidth) = true →
        next (LLVM.ByteType.mk bitwidth : TypeAttr) := by
  rw [TypeMatcher.denote_type]
  constructor
  · intro h bitwidth hmatcher
    exact h (LLVM.ByteType.mk bitwidth) hmatcher
  · intro h type hmatcher
    rcases type with ⟨bitwidth⟩
    exact h bitwidth hmatcher

@[simp 2000]
theorem TypeMatcher.denote_modArith (matcher : ModArithType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? ModArithType).map matcher).getD false) next ↔
      ∀ type : ModArithType, matcher type = true → next type := by
  exact TypeMatcher.denote_type matcher next

@[simp 2000]
theorem TypeMatcher.denote_register (matcher : RegisterType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? RegisterType).map matcher).getD false) next ↔
      ∀ type : RegisterType, matcher type = true → next type := by
  exact TypeMatcher.denote_type matcher next

@[simp 2000]
theorem TypeMatcher.denote_pointer (matcher : LLVM.PointerType → Bool)
    (next : TypeAttr → Prop) :
    TypeMatcher.denote
        (fun attr => ((attr.cast? LLVM.PointerType).map matcher).getD false) next ↔
      ∀ type : LLVM.PointerType, matcher type = true → next type := by
  exact TypeMatcher.denote_type matcher next

theorem CreateProg.Supported.of_mem
    {prog : CreateProg OpCode α} (hsupported : prog.Supported)
    {decl : CreateDecl OpCode} (hmem : decl ∈ prog.decls) : decl.Supported := by
  have aux : ∀ decls : List (CreateDecl OpCode),
      CreateProg.DeclsSupported decls → decl ∈ decls → decl.Supported := by
    intro decls hsupported hmem
    induction decls with
    | nil => simp at hmem
    | cons head tail ih =>
      simp only [CreateProg.DeclsSupported] at hsupported
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hsupported.1
      · exact ih hsupported.2 hmem
  exact aux prog.decls hsupported hmem

theorem CreateDecl.denoteResults_operation_eq_some_iff :
    CreateDecl.denoteResults
        (.operation opCode operands resultTypeHandles propertyHandle opHandle resultHandles)
          assignment =
      some results ↔
    ∃ operandValues resultTypes actual memory,
      assignment.getValues operands = some operandValues ∧
      assignment.getTypes resultTypeHandles = some resultTypes ∧
      assignment.getProperty propertyHandle = some actual ∧
      interpretOp' opCode actual resultTypes operandValues #[] .empty =
        .ok (results, memory, none) := by
  constructor
  · intro h
    simp only [CreateDecl.denoteResults] at h
    cases hoperands : assignment.getValues operands with
    | none => simp [hoperands] at h
    | some operandValues =>
      rw [hoperands] at h
      cases htypes : assignment.getTypes resultTypeHandles with
      | none => simp [htypes] at h
      | some resultTypes =>
        rw [htypes] at h
        cases hactual : assignment.getProperty propertyHandle with
        | none => simp [hactual] at h
        | some actual =>
          rw [hactual] at h
          simp at h
          generalize hinterpret :
              interpretOp' opCode actual resultTypes operandValues #[] .empty = interpreted at h
          cases interpreted with
          | fail => simp at h
          | ub => simp at h
          | ok result =>
            rcases result with ⟨interpretedResults, memory, controlFlow⟩
            cases controlFlow with
            | some action => simp at h
            | none =>
              simp only [Option.some.injEq] at h
              subst interpretedResults
              exact ⟨operandValues, resultTypes, actual, memory,
                rfl, rfl, rfl, hinterpret⟩
  · rintro ⟨operandValues, resultTypes, actual, memory,
      hoperands, htypes, hactual, hinterpret⟩
    simp [CreateDecl.denoteResults, hoperands, htypes, hactual, hinterpret]

/-! `puddle_simp` unfolds pointwise matcher models into the algebraic obligation written by the
rule author. -/
private meta def tryUnfoldMatcherTarget (goal : Lean.MVarId) (matcherName : Lean.Name) :
    Lean.Meta.MetaM Lean.MVarId := do
  try
    Lean.Meta.unfoldTarget goal matcherName
  catch _ =>
    return goal

private meta def tryUnfoldMatcherLocal (goal : Lean.MVarId) (fvarId : Lean.FVarId)
    (matcherName : Lean.Name) : Lean.Meta.MetaM Lean.MVarId := do
  try
    Lean.Meta.unfoldLocalDecl goal fvarId matcherName
  catch _ =>
    return goal

open Lean Elab Tactic Meta in
/-- Unfold the matcher stored by a closed Puddle rule, if it is a named definition. -/
elab "puddle_unfold_rule_matcher" rule:term : tactic => withMainContext do
  let ruleExpr ← elabTerm rule none
  let some matcherExpr ← reduceProj? (mkProj ``Pattern 1 ruleExpr) | return
  let some matcherName := matcherExpr.getAppFn.constName? | return
  if matcherName == ``MatchProg.build then return
  let localDecls := (← getLCtx).decls.toArray
  let mut goal ← getMainGoal
  for localDecl? in localDecls do
    let some localDecl := localDecl? | continue
    goal ← tryUnfoldMatcherLocal goal localDecl.fvarId matcherName
  goal ← tryUnfoldMatcherTarget goal matcherName
  replaceMainGoal [goal]

private meta partial def casesModelFacts (goal : Lean.MVarId) : Lean.Meta.MetaM (List Lean.MVarId) :=
  goal.withContext do
    let localCtx ← Lean.getLCtx
    for localDecl? in localCtx.decls do
      let some localDecl := localDecl? | continue
      let type ← Lean.Meta.whnf localDecl.type
      if localDecl.isAuxDecl && !type.isAppOfArity ``Exists 2 then continue
      let variableEquality :=
        type.isAppOfArity ``Eq 3 &&
          (type.getAppArgs[1]!.isFVar || type.getAppArgs[2]!.isFVar)
      if type.isAppOfArity ``And 2 || type.isAppOfArity ``Exists 2 || variableEquality then
        let subgoals ← goal.cases localDecl.fvarId
        let mut result := []
        for subgoal in subgoals do
          result := result ++ (← casesModelFacts subgoal.mvarId)
        return result
    return [goal]

open Lean Elab Tactic Meta in
/-- Recursively expose conjunctions and witnesses supplied by pointwise matcher models. -/
elab "puddle_cases_models" : tactic => withMainContext do
  let goal ← getMainGoal
  let goals ← casesModelFacts goal
  replaceMainGoal goals

macro "puddle_simp" "[" rule:ident "]" : tactic =>
  `(tactic| (
    unfold Pattern.Valid Pattern.DenotationallyValid
    constructor
    · unfold $rule
      puddle_unfold_rule_matcher $rule
      simp [MatchProg.Supported, MatchDecl.Supported, MatchDecl.SupportsRoot,
        PropertyMatcher.Supported,
        Pattern.Builder, MatchProg.build, MatchProg.type, MatchProg.value,
        MatchProg.operation, MatchProg.guard, MatchProg.root, bind, pure]
      all_goals subst_vars <;> try simp_all
      all_goals try grind
    constructor
    · unfold $rule
      puddle_unfold_rule_matcher $rule
      simp [CreateProg.Supported, CreateProg.DeclsSupported, CreateDecl.Supported,
        Pattern.Builder, CreateProg.empty, CreateProg.build, CreateProg.property,
        CreateProg.operation,
        CreateProg.applyNative,
        bind, pure]
      all_goals native_decide
    intro assignment hmodels
    unfold $rule at hmodels ⊢
    puddle_unfold_rule_matcher $rule
    simp (config := { maxSteps := 300000 })
      [MatchProg.Models, MatchDecl.Models, MatchDecl.ResultsModel,
      PropertyMatcher.Models, PropertyMatcher.Interprets,
      Pattern.Builder, MatchProg.build, MatchProg.type, MatchProg.value,
      MatchProg.operation, MatchProg.guard, MatchProg.root,
      CreateProg.empty, CreateProg.build, CreateProg.property, CreateProg.operation,
      CreateProg.applyNative,
      CreateProg.denote, CreateProg.evalDecls,
      CreateDecl.eval, CreateDecl.denoteResults,
      Replacement.refinesRoot,
      RuntimeValue.isRefinedBy, Option.bind_eq_some_iff,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      Array.mapM_eq_mapM_toList,
      SemanticCreateAssignment.bindValues,
      SemanticCreateAssignment.getOp, SemanticCreateAssignment.getValue,
      SemanticCreateAssignment.getType, SemanticCreateAssignment.getProperty,
      SemanticCreateAssignment.getProperty_bindProperty_self,
      SemanticCreateAssignment.getValue_bindValue_of_eq,
      SemanticCreateAssignment.getValue_bindValue_of_ne,
      SemanticCreateAssignment.getValue_bindOp_of_eq,
      SemanticCreateAssignment.getValue_bindOp_of_ne,
      SemanticCreateAssignment.getValue_bindProperty_of_ne,
      SemanticCreateAssignment.getOp_bindProperty_of_ne,
      SemanticCreateAssignment.getType_bindProperty_of_ne,
      SemanticCreateAssignment.getProperty_bindProperty_of_eq,
      SemanticAssignment.getValue_bindValue_of_eq,
      SemanticAssignment.getValue_bindValue_of_ne,
      SemanticAssignment.getValue_bindOp_of_eq,
      SemanticAssignment.getValue_bindOp_of_ne,
      SemanticAssignment.getValue_bindProperty_of_ne,
      SemanticAssignment.getProperty_bindProperty_of_eq,
      SemanticAssignment.getProperty_bindProperty_self,
      instMetadataStoreOpCodeSemanticCreateAssignment,
      default, instInhabitedBool.default,
      bind, pure] at hmodels ⊢
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals simp_all (config := { maxSteps := 300000 })
      [PropertyMatcher.Interprets,
      CreateProg.denote, CreateProg.evalDecls,
      CreateDecl.eval, CreateDecl.denoteResults,
      Replacement.refinesRoot,
      RuntimeValue.isRefinedBy, Option.bind_eq_some_iff,
      SemanticAssignment.getValues, SemanticAssignment.getTypes,
      Array.mapM_eq_mapM_toList,
      SemanticCreateAssignment.bindValues,
      SemanticCreateAssignment.getOp, SemanticCreateAssignment.getValue,
      SemanticCreateAssignment.getType, SemanticCreateAssignment.getProperty,
      SemanticCreateAssignment.getProperty_bindProperty_self,
      SemanticCreateAssignment.getValue_bindValue_of_eq,
      SemanticCreateAssignment.getValue_bindValue_of_ne,
      SemanticCreateAssignment.getValue_bindOp_of_eq,
      SemanticCreateAssignment.getValue_bindOp_of_ne,
      SemanticCreateAssignment.getValue_bindProperty_of_ne,
      SemanticCreateAssignment.getOp_bindProperty_of_ne,
      SemanticCreateAssignment.getType_bindProperty_of_ne,
      SemanticCreateAssignment.getProperty_bindProperty_of_eq,
      SemanticAssignment.getValue_bindValue_of_eq,
      SemanticAssignment.getValue_bindValue_of_ne,
      SemanticAssignment.getValue_bindOp_of_eq,
      SemanticAssignment.getValue_bindOp_of_ne,
      SemanticAssignment.getValue_bindProperty_of_ne,
      SemanticAssignment.getProperty_bindProperty_of_eq,
      SemanticAssignment.getProperty_bindProperty_self,
      instMetadataStoreOpCodeSemanticCreateAssignment,
      default, instInhabitedBool.default,
      bind, pure]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all
    all_goals try simp_all [interpretOp', Arith.interpretOp', bind, pure]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all [interpretOp', Arith.interpretOp', bind, pure]
    all_goals puddle_cases_models
    all_goals subst_vars
    all_goals try simp_all [RuntimeValue.isRefinedBy]))


end

end Veir.Puddle
