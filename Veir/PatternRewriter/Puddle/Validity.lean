module

public import Veir.PatternRewriter.Puddle.Execution
public import Veir.PatternRewriter.Puddle.Builders
public import Veir.Interpreter.Evaluate
public import Veir.PatternRewriter.Semantics

import Veir.Data.Refinement
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Attribute
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics

/-! Denotational semantics and the author-facing validity obligation for Puddle rules. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
Whether a matcher property has an interpreter correspondence in the prototype.

Any single-result operation is admitted when every property value accepted by the matcher is
declared to have no memory effects.
-/
@[expose]
def PropertyMatcher.Supported {opCode : OpCode} (property : PropertyMatcher opCode)
  (_numOperands numResults : Nat) : Prop :=
  numResults = 1 ∧
    ∀ actual, property actual = true →
      HasOpInfo.getEffects opCode actual == .none

/-- Syntactic support boundary for declarations admitted by denotational validity. -/
@[expose]
def MatchDecl.Supported (decl : MatchDecl OpCode) : Prop :=
  match decl with
  | .operation _opCode ops retTypes property _ _ results =>
    property.Supported ops.size retTypes.size ∧
      (results.size = retTypes.size ∨ results = #[])
  | _ => True


/-! ## Denotational validity

This interpretation is deliberately separate from `Pattern`: pattern authors only write the matcher
and replacement. The interpreter below turns those two pieces of syntax into the proposition they
must prove. -/

inductive SemanticBinding where
| op (results : Array RuntimeValue)
| value (value : RuntimeValue)
| type (type : TypeAttr)
| property (opCode : OpCode) (value : propertiesOf opCode)

abbrev SemanticAssignment := Array (Option SemanticBinding)

@[expose]
def SemanticAssignment.empty (size : Nat) : SemanticAssignment :=
  Array.replicate size none

@[expose]
def SemanticAssignment.bind (assignment : SemanticAssignment)
    (id : Nat) (binding : SemanticBinding) : SemanticAssignment :=
  assignment.setIfInBounds id (some binding)

@[expose]
def SemanticAssignment.bindOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) (results : Array RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.op results)

@[expose]
def SemanticAssignment.bindValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) (value : RuntimeValue) : SemanticAssignment :=
  assignment.bind handle.id (.value value)

@[expose]
def SemanticAssignment.bindType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) (type : TypeAttr) : SemanticAssignment :=
  assignment.bind handle.id (.type type)

@[expose]
def SemanticAssignment.bindProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) : SemanticAssignment :=
  assignment.bind handle.id (.property opCode value)

@[expose]
def SemanticAssignment.bindValues (assignment : SemanticAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) : SemanticAssignment :=
  match handles, values with
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => assignment

@[expose]
def SemanticAssignment.getOp (assignment : SemanticAssignment)
    (handle : Handle OpCode .op) : Option (Array RuntimeValue) :=
  match assignment[handle.id]? with
  | some (some (.op results)) => some results
  | _ => none

@[expose]
def SemanticAssignment.getValue (assignment : SemanticAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment[handle.id]? with
  | some (some (.value value)) => some value
  | _ => none

@[expose]
def SemanticAssignment.getType (assignment : SemanticAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  match assignment[handle.id]? with
  | some (some (.type type)) => some type
  | _ => none

@[expose]
def SemanticAssignment.getProperty (assignment : SemanticAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  match assignment[handle.id]? with
  | some (some (.property actualOpCode value)) =>
    if h : actualOpCode = opCode then
      some (h ▸ value)
    else none
  | _ => none

@[expose]
def SemanticAssignment.getValues (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .value)) : Option (Array RuntimeValue) :=
  handles.mapM assignment.getValue

@[expose]
def SemanticAssignment.getTypes (assignment : SemanticAssignment)
    (handles : Array (Handle OpCode .type)) : Option (Array TypeAttr) :=
  handles.mapM assignment.getType

abbrev SemanticCreateBinding := SemanticBinding
abbrev SemanticCreateAssignment := SemanticAssignment

@[expose]
def SemanticCreateAssignment.bind (assignment : SemanticCreateAssignment)
    (id : Nat) (binding : SemanticCreateBinding) : SemanticCreateAssignment :=
  if h : id < assignment.size then
    assignment.set id (some binding)
  else
    assignment ++ Array.replicate (id - assignment.size) none ++ #[some binding]

@[expose]
def SemanticCreateAssignment.bindOp (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .op) (results : Array RuntimeValue) : SemanticCreateAssignment :=
  assignment.bind handle.id (.op results)

@[expose]
def SemanticCreateAssignment.bindValue (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .value) (value : RuntimeValue) : SemanticCreateAssignment :=
  assignment.bind handle.id (.value value)

@[expose]
def SemanticCreateAssignment.bindType (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) (type : TypeAttr) : SemanticCreateAssignment :=
  assignment.bind handle.id (.type type)

@[expose]
def SemanticCreateAssignment.bindProperty (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) (value : propertiesOf opCode) :
    SemanticCreateAssignment :=
  assignment.bind handle.id (.property opCode value)

@[expose, simp]
def SemanticCreateAssignment.bindValues (assignment : SemanticCreateAssignment)
    (handles : List (Handle OpCode .value)) (values : List RuntimeValue) :
    SemanticCreateAssignment :=
  match handles, values with
  | handle :: handles, value :: values =>
    (assignment.bindValue handle value).bindValues handles values
  | _, _ => assignment

@[expose]
def SemanticCreateAssignment.getOp (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .op) : Option (Array RuntimeValue) :=
  match assignment[handle.id]? with
  | some (some (.op results)) => some results
  | _ => none

@[expose]
def SemanticCreateAssignment.getValue (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .value) : Option RuntimeValue :=
  match assignment[handle.id]? with
  | some (some (.value value)) => some value
  | _ => none

@[expose, simp]
def SemanticCreateAssignment.getType (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode .type) : Option TypeAttr :=
  SemanticAssignment.getType assignment handle

@[expose, simp]
def SemanticCreateAssignment.getProperty (assignment : SemanticCreateAssignment)
    (handle : Handle OpCode (.prop opCode)) : Option (propertiesOf opCode) :=
  SemanticAssignment.getProperty assignment handle

instance : MetadataStore OpCode SemanticCreateAssignment where
  getType := SemanticCreateAssignment.getType
  getProperty := fun store {_opCode} propertyHandle =>
    SemanticCreateAssignment.getProperty store propertyHandle
  bindType := fun store typeHandle value =>
    some (SemanticCreateAssignment.bindType store typeHandle value)
  bindProperty := fun store {_opCode} propertyHandle value =>
    some (SemanticCreateAssignment.bindProperty store propertyHandle value)

/-- Interpreter-backed denotation used for effect-free operations without a specialized Puddle
denotation.  Successors and control flow are existential because matcher syntax records neither;
the result values are the observable part used by a rewrite. -/
@[expose]
def PropertyMatcher.Interprets (opCode : OpCode) (actual : propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  ∃ successors memory controlFlow,
    interpretOp' opCode actual resultTypes operands successors memory =
      .ok (results, memory, controlFlow)

@[expose]
def PropertyMatcher.denote {opCode : OpCode} (property : PropertyMatcher opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (next : propertiesOf opCode → Array RuntimeValue → Prop) : Prop :=
  ∀ actual, property actual = true →
    ∀ results, PropertyMatcher.Interprets opCode actual resultTypes operands results →
      next actual results

@[expose]
def TypeMatcher.denote (matcher : TypeMatcher) (next : TypeAttr → Prop) : Prop :=
  ∀ type, matcher type = true → next type

/-- Interpret one matcher declaration, passing its semantic binding to the rest of the program.

An unsupported or ill-formed semantic path is rejected with `False`; it cannot make validity
vacuously true. -/
@[expose]
def MatchDecl.denote (decl : MatchDecl OpCode) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) : Prop :=
  match decl with
  | .root _ => next assignment
  | .type matcher handle =>
      matcher.denote fun type => next (assignment.bindType handle type)
  | .value typeHandle handle =>
    match assignment.getType typeHandle with
    | some typeAttr =>
      match typeAttr.val with
      | .integerType intType => ∀ value : Data.LLVM.Int intType.bitwidth,
          next (assignment.bindValue handle (.int intType.bitwidth value))
      | .floatType floatType => ∀ value : Float,
          next (assignment.bindValue handle (.float floatType.bitwidth value))
      | .byteType byteType => ∀ value : Data.LLVM.Byte byteType.bitwidth,
          next (assignment.bindValue handle (.byte byteType.bitwidth value))
      | Attribute.modArithType modType =>
          ∀ value : Data.LLVM.Int modType.modulus.type.bitwidth,
            next (assignment.bindValue handle (.int modType.modulus.type.bitwidth value))
      | Attribute.registerType _ => ∀ value : Data.RISCV.Reg,
          next (assignment.bindValue handle (.reg value))
      | Attribute.llvmPointerType _ => ∀ value : UInt64,
          next (assignment.bindValue handle (.addr value))
      | _ => False
    | none => False
  | .operation _opCode operandHandles returnTypeHandles property propertyHandle handle resultHandles =>
    match assignment.getValues operandHandles, assignment.getTypes returnTypeHandles with
    | some ops, some retTypes =>
      property.denote retTypes ops fun actualProperty results =>
        next (((assignment.bindProperty propertyHandle actualProperty).bindOp handle results).bindValues
          resultHandles.toList results.toList)
    | _, _ => False
  | @MatchDecl.guard _ _ _ inputBundle inputs predicate =>
    match MetadataTuple.resolve (self := inputBundle) assignment inputs with
    | some values => predicate values = true → next assignment
    | none => False
  | .operands _ _ => next assignment
  | .resultTypes _ _ => next assignment

@[expose]
def MatchProg.denoteDecls (decls : List (MatchDecl OpCode))
    (assignment : SemanticAssignment) (result : SemanticAssignment → Prop) : Prop :=
  match decls with
  | [] => result assignment
  | (@MatchDecl.guard _ _ Inputs inputBundle inputs predicate) :: decls =>
      MatchProg.denoteDecls decls assignment fun assignment =>
        (@MatchDecl.guard _ _ Inputs inputBundle inputs predicate).denote assignment result
  | decl :: decls => decl.denote assignment fun assignment =>
      MatchProg.denoteDecls decls assignment result

@[expose]
def MatchProg.root? (prog : MatchProg OpCode α) : Option (Handle OpCode .op) :=
  prog.decls.findSome? fun
    | .root root => some root
    | _ => none


@[expose]
def PropertyMatcher.Models {opCode : OpCode} (property : PropertyMatcher opCode)
    (actual : propertiesOf opCode)
    (_resultTypes : Array TypeAttr) (operands results : Array RuntimeValue) : Prop :=
  property actual = true ∧
    PropertyMatcher.Interprets opCode actual _resultTypes operands results

@[expose]
def MatchDecl.ResultsModel (assignment : SemanticAssignment)
    (resultHandles : Array (Handle OpCode .value)) (results : Array RuntimeValue) : Prop :=
  resultHandles = #[] ∨ assignment.getValues resultHandles = some results

@[expose]
def MatchDecl.Models (decl : MatchDecl OpCode) (assignment : SemanticAssignment) : Prop :=
  match decl with
  | .root handle => (assignment.getOp handle).isSome
  | .type matcher handle =>
    ∃ type, assignment.getType handle = some type ∧ matcher type = true
  | .value typeHandle handle =>
    ∃ type value,
      assignment.getType typeHandle = some type ∧
      assignment.getValue handle = some value ∧
      value.Conforms type
  | .operation _opCode operandHandles returnTypeHandles property propertyHandle handle resultHandles =>
    ∃ operands resultTypes results actualProperty,
      assignment.getValues operandHandles = some operands ∧
      assignment.getTypes returnTypeHandles = some resultTypes ∧
      assignment.getOp handle = some results ∧
      assignment.getProperty propertyHandle = some actualProperty ∧
      MatchDecl.ResultsModel assignment resultHandles results ∧
      property.Models actualProperty resultTypes operands results
  | @MatchDecl.guard _ _ _ inputBundle inputs predicate =>
    ∃ values,
      MetadataTuple.resolve (self := inputBundle) assignment inputs = some values ∧
      predicate values = true
  | .operands opHandle results =>
    ∃ op, assignment.getOp opHandle = some op ∧ assignment.getValues results = some op
  | .resultTypes opHandle _ =>
    (assignment.getOp opHandle).isSome

/-- Whether an operation declaration is the supported constraint paired with a root handle. -/
@[expose]
def MatchDecl.SupportsRoot (decl : MatchDecl OpCode) (rootHandle : Handle OpCode .op) : Prop :=
  match decl with
  | .operation opCode _ _ _ _ opHandle _ =>
      opHandle = rootHandle ∧ HasOpInfo.isTerminator opCode = false
  | _ => False

/-- Pointwise semantic facts for every matcher declaration.

There is deliberately no assignment-size invariant here: each successful `getType`, `getValue`,
`getOp`, or `getProperty` fact already proves that the handle has a binding of the expected kind. -/
@[expose]
def MatchProg.Models (prog : MatchProg OpCode α) (assignment : SemanticAssignment) : Prop :=
  ∀ decl ∈ prog.decls, decl.Models assignment

/-- Every declaration in the matcher is covered by the prototype's denotation. -/
@[expose]
def MatchProg.Supported (prog : MatchProg OpCode α) : Prop :=
  (∀ decl ∈ prog.decls, decl.Supported) ∧
  ∀ rootHandle, .root rootHandle ∈ prog.decls →
    ∃ decl ∈ prog.decls, decl.SupportsRoot rootHandle


@[expose]
def Replacement.refinesRoot (replacement : Replacement OpCode) (root : Handle OpCode .op)
    (matched final : SemanticAssignment) : Prop :=
  match matched.getOp root, final.getValues replacement.values with
  | some rootResults, some replacementValues => rootResults ⊒ replacementValues
  | _, _ => False

/-- Creation is supported for effect-free operations with ordinary fallthrough control flow. -/
@[expose]
def CreateDecl.Supported : CreateDecl OpCode → Prop
  | .operation opCode _ _ _ _ _ =>
    HasOpInfo.isTerminator opCode = false ∧
      ∀ actual, HasOpInfo.getEffects opCode actual == .none
  | .property _ _ _ => True
  | @CreateDecl.applyNative _ _ _ _ _ _ _ _ _ => True

/-- Every declaration in a creation program is supported. -/
@[expose]
def CreateProg.DeclsSupported : List (CreateDecl OpCode) → Prop
  | [] => True
  | decl :: decls => decl.Supported ∧ CreateProg.DeclsSupported decls

@[expose]
def CreateProg.Supported (prog : CreateProg OpCode α) : Prop :=
  CreateProg.DeclsSupported prog.decls

/-- Evaluate a created operation using the generic interpreter and a canonical empty memory. -/
@[expose]
def CreateDecl.denoteResults :
    CreateDecl OpCode → SemanticAssignment → Option (Array RuntimeValue)
  | .operation opCode operands resultTypeHandles properties _ _, assignment => do
      let values ← assignment.getValues operands
      let resultTypes ← assignment.getTypes resultTypeHandles
      let properties ← assignment.getProperty properties
      match interpretOp' opCode properties resultTypes values #[] .empty with
      | .ok (results, _, none) => some results
      | _ => none
  | _, _ => none

/-- Evaluate one declaration and bind its semantic operation and result handles. -/
@[expose]
def CreateDecl.eval (decl : CreateDecl OpCode) (assignment : SemanticAssignment) :
    Option SemanticAssignment :=
  match decl with
  | .property _ value result =>
    some (SemanticCreateAssignment.bindProperty assignment result value)
  | .operation _ _ _ _ opHandle resultHandles =>
    match decl.denoteResults assignment with
    | some results =>
      some ((SemanticCreateAssignment.bindOp assignment opHandle results).bindValues
        resultHandles.toList results.toList)
    | none => none
  | @CreateDecl.applyNative _ _ _ _ inputBundle outputBundle inputs rewrite outputs => do
    let values ← MetadataTuple.resolve (self := inputBundle) assignment inputs
    let outputValues ← rewrite values
    MetadataTuple.bind (self := outputBundle) assignment outputs outputValues

/-- Evaluate declarations in creation order. -/
@[expose]
def CreateProg.evalDecls (decls : List (CreateDecl OpCode)) (assignment : SemanticAssignment) :
    Option SemanticAssignment :=
  match decls with
  | [] => some assignment
  | decl :: decls => do
    let assignment ← decl.eval assignment
    CreateProg.evalDecls decls assignment

/-- Pass the completed semantic creation assignment to the terminal validity obligation. -/
@[expose]
def CreateProg.denote (prog : CreateProg OpCode α) (assignment : SemanticAssignment)
    (next : SemanticAssignment → Prop) : Prop :=
  match CreateProg.evalDecls prog.decls assignment with
  | some assignment => next assignment
  | none => True

/-- The denotational proposition derived from a rule's matcher and replacement.

No operational preservation proof is stored here. Pattern authors prove only this algebraic
obligation; the generic compiler theorem derives `PreservesSemantics`. -/
@[expose]
def Pattern.DenotationallyValid (rule : Pattern OpCode) : Prop :=
  rule.matcher.Supported ∧
    rule.creation.Supported ∧
    match rule.matcher.root? with
    | none => False
    | some root =>
      ∀ assignment, rule.matcher.Models assignment →
        rule.creation.denote assignment fun final =>
          rule.replacement.refinesRoot root assignment final

/-- Public rule validity. `puddle_simp` keeps the semantic assignment used by this definition
entirely behind the tactic boundary. -/
@[expose]
def Pattern.Valid (rule : Pattern OpCode) : Prop :=
  rule.DenotationallyValid
end

end Veir.Puddle
