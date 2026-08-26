module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLVM.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive GMIR where
  | g_add
  | g_sub
  | g_icmp
  deriving Inhabited, Repr, Hashable, DecidableEq

-- We don't represent 'unknown' (special) or immediate types. See comment for GMIR.genericOpInfo.
inductive TypeGroup where
  | type (id : Nat)
  | ptype (id : Nat)
  deriving Inhabited, Repr, BEq, DecidableEq, Hashable

structure GenericOpInfo where
  outOperandList : Array TypeGroup
  inOperandList : Array TypeGroup
  deriving Inhabited, Repr

/--
Mirrors LLVM's GenericOpcodes.td.
Operands labeled as unknown or immediate type in LLVM's GenericOpcodes.td are omitted here and are represented in the
operations properties instead.

https://github.com/llvm/llvm-project/blob/9cf1fbf72aaef723d68e078e3ffee6ed8b3cbe3d/llvm/include/llvm/Target/GenericOpcodes.td
-/
def GMIR.genericOpInfo : GMIR → GenericOpInfo
  | .g_add | .g_sub =>
    { outOperandList := #[.type 0]
      inOperandList  := #[.type 0, .type 0] }
  | .g_icmp =>
    { outOperandList := #[.type 0]
      inOperandList  := #[.type 1, .type 1] }

@[expose, properties_of]
def GMIR.propertiesOf : GMIR → Type
  | .g_add | .g_sub => NswNuwProperties
  | .g_icmp         => IcmpProperties

def GMIR.fromAttrDict
    (op : GMIR) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (GMIR.propertiesOf op) := by
  cases op with
  | g_add | g_sub => exact NswNuwProperties.fromAttrDict attrDict
  | g_icmp => exact IcmpProperties.fromAttrDict attrDict

def GMIR.toAttrDict
    (op : GMIR) (props : GMIR.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .g_add | .g_sub => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    let val := (if props.nsw then 1 else 0) + (if props.nuw then 2 else 0)
    if val > 0 then
      dict := dict.insert "overflowFlags".toUTF8
        (.integerAttr (IntegerAttr.mk (Int.ofNat val) (IntegerType.mk 32)))
    dict
  | .g_icmp =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.mk 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)

#generate_dialect GMIR

instance : IsOpCode GMIR where
  fromName    := GMIR.fromName
  name        := GMIR.name
  propertiesOf := GMIR.propertiesOf
  fromAttrDict := GMIR.fromAttrDict
  toAttrDict   := GMIR.toAttrDict

-- Mirror of `MachineVerifier::verifyPreISelGenericInstruction`.
def GMIR.verifyPreISelGenericInstruction {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR] (op : GMIR) (opPtr : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : opPtr.InBounds ctx.raw) :
    Except String PUnit := do
  let info := op.genericOpInfo
  let typedGroups := info.outOperandList.zip (opPtr.getResultTypes! ctx.raw) ++
                     info.inOperandList.zip (opPtr.getOperandTypes! ctx.raw)

  let canon : Std.HashMap TypeGroup TypeAttr :=
    typedGroups.foldr (init := {}) fun (slot, ty) canon => canon.insert slot ty

  for (group, type) in typedGroups do
    let expected := canon[group]!
    if expected != type then
      let name := String.fromUTF8! (IsOpCode.name (opPtr.getOpType ctx.raw opIn))
      throw s!"{name}: type mismatch: expected {expected}, got {type}"

def GMIR.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR] (op : GMIR) (opPtr : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : opPtr.InBounds ctx.raw) :
    Except String PUnit :=
  GMIR.verifyPreISelGenericInstruction op opPtr ctx opIn

def GMIR.getEffects (_op : GMIR) (_props : GMIR.propertiesOf _op) : MemoryEffects :=
  .none

def GMIR.isConstantLike : GMIR → Bool
  | _ => false

def GMIR.hasSSADominance (_op : GMIR) (_index : Nat) : Bool :=
  true

instance : HasOpInfo GMIR where
  verifyLocalInvariants := GMIR.verifyLocalInvariants
  getEffects      := GMIR.getEffects
  isConstantLike  := GMIR.isConstantLike
  hasSSADominance := GMIR.hasSSADominance

end

end Veir
