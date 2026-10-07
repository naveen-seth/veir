module

public import Veir.IR.Attribute
public import Std.Data.HashMap

namespace Veir

public section

/--
Properties of `gmir.g_sext_inreg`: the operand is sign-extended from its low `sz` bits.
LLVM's `G_SEXT_INREG` has `sz` as an immediate operand.
-/
structure SextInRegProperties where
  sz : Nat
deriving Inhabited, Repr, Hashable, DecidableEq

def SextInRegProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String SextInRegProperties := do
  if attrDict.size > 1 then
    throw s!"gmir.g_sext_inreg: expected only 'sz' property, but got {attrDict.size} properties"
  let some attr := attrDict["sz".toUTF8]?
    | throw "gmir.g_sext_inreg: missing 'sz' property"
  let .integerAttr intAttr := attr
    | throw s!"gmir.g_sext_inreg: expected 'sz' to be an integer attribute, but got {attr}"
  if intAttr.value < 0 then
    throw s!"gmir.g_sext_inreg: expected 'sz' to be nonnegative, but got {intAttr.value}"
  return { sz := intAttr.value.toNat }

def SextInRegProperties.toAttrDict (props : SextInRegProperties) :
    Std.HashMap ByteArray Attribute :=
  (Std.HashMap.emptyWithCapacity 1).insert "sz".toUTF8
    (.integerAttr (IntegerAttr.mk (Int.ofNat props.sz) (IntegerType.signless 64)))

end

end Veir
