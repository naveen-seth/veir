module

/- FunctionOpInterface

  This file provides the `FunctionOpInterface` interface, which provides support
  for interacting with operations that behave like functions.
  Currently, this supports llvm.func and func.func.

  Also see:
  https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/Interfaces/FunctionInterfaces.td
-/

public import Veir.GlobalOpInfo
public import Veir.IR.Fields

namespace Veir

public section

namespace FuncOpInterface

/-- Returns the symbol name of the function. -/
public def funcSymName? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option StringAttr :=
  match funcOp.getOpType! raw with
  | .func .func =>
    (funcOp.getProperties! raw (.func .func) : FuncFuncProperties).sym_name
  | .llvm .func =>
    (funcOp.getProperties! raw (.llvm .func) : LLVMFuncProperties).sym_name
  | _ => none

/-- Returns the type of the function. -/
public def getFunctionType? (funcOp : OperationPtr) (raw : IRContext OpCode) :
    Option FunctionType := do
  match funcOp.getOpType! raw with
  | .func .func =>
    let ta ← (funcOp.getProperties! raw (.func .func) : FuncFuncProperties).function_type
    match ta.val with
    | .functionType ft => some ft
    | _ => none
  | .llvm .func =>
    let ta ← (funcOp.getProperties! raw (.llvm .func) : LLVMFuncProperties).function_type
    match ta.val with
    | .llvmFunctionType ft => some ft
    | _ => none
  | _ => none

/-
  Body Handling
-/

/-- Return the region containing the body of this function. -/
public def getFunctionBody (funcOp : OperationPtr) (raw : IRContext OpCode)
    (opInBounds : funcOp.InBounds raw := by grind)
    (hasRegion : 0 < funcOp.getNumRegions raw opInBounds := by grind) : RegionPtr :=
  funcOp.getRegion raw 0 opInBounds hasRegion

public def getFunctionBody! (funcOp : OperationPtr) (raw : IRContext OpCode) : RegionPtr :=
  funcOp.getRegion! raw 0

@[grind =_, eq_bang ←]
theorem getFunctionBody!_eq_getFunctionBody {funcOp : OperationPtr} {raw : IRContext OpCode}
    {opInBounds} (hasRegion : 0 < funcOp.getNumRegions raw opInBounds) :
    getFunctionBody! funcOp raw = getFunctionBody funcOp raw opInBounds hasRegion := by
  grind [getFunctionBody, getFunctionBody!]

theorem getFunctionBody!_inBounds
    (ctxInBounds : raw.FieldsInBounds)
    (opInBounds : funcOp.InBounds raw)
    (hasRegion : 0 < funcOp.getNumRegions! raw) :
    (getFunctionBody! funcOp raw).InBounds raw := by
  grind [getFunctionBody!, OperationPtr.getRegions!_inBounds]

grind_pattern getFunctionBody!_inBounds => (getFunctionBody! funcOp raw), raw.FieldsInBounds

/-- Returns true if this function has no blocks within the body. -/
public def isEmpty (funcOp : OperationPtr) (raw : IRContext OpCode)
    (opInBounds : funcOp.InBounds raw := by grind)
    (hasRegion : 0 < funcOp.getNumRegions raw opInBounds := by grind)
    (regionInBounds : (getFunctionBody funcOp raw opInBounds hasRegion).InBounds raw := by grind) : Bool :=
  ((getFunctionBody funcOp raw opInBounds hasRegion).get raw regionInBounds).firstBlock.isNone

public def isEmpty! (funcOp : OperationPtr) (raw : IRContext OpCode) : Bool :=
  ((getFunctionBody! funcOp raw).get! raw).firstBlock.isNone

@[grind =_, eq_bang ←]
theorem isEmpty!_eq_isEmpty {funcOp : OperationPtr} {raw : IRContext OpCode}
    {opInBounds} (hasRegion : 0 < funcOp.getNumRegions raw opInBounds)
    (regionInBounds : (getFunctionBody funcOp raw opInBounds hasRegion).InBounds raw) :
    isEmpty! funcOp raw = isEmpty funcOp raw opInBounds hasRegion regionInBounds := by
  grind [isEmpty, isEmpty!]

/-- Returns true if this function is external, i.e. it has no body. -/
public abbrev isExternal  := @isEmpty
public abbrev isExternal! := @isEmpty!

/-
  Argument and Result Handling
-/

/-- Returns the number of function arguments. -/
public def getNumArguments? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option Nat := do
  rlet ft ← getFunctionType? funcOp raw
  ft.inputs.size

/-- Returns the number of function results. -/
public def getNumResults? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option Nat := do
  rlet ft ← getFunctionType? funcOp raw
  ft.outputs.size

/-- Returns the block arguments of the function body entry block (if present). -/
public def getArguments? (funcOp : OperationPtr) (raw : IRContext OpCode) : Option (Array ValuePtr) := do
  rlet block ← ((getFunctionBody! funcOp raw).get! raw).firstBlock
  block.getArguments! raw

end FuncOpInterface

end -- public section

end Veir
