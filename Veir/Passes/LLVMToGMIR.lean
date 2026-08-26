module

public import Veir.Pass
import Veir.Passes.Matching
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/-!
  This file replicates LLVM's GlobalISel IRTranslator pass.
  This pass is responsible for translating LLVM IR into gMIR.

  The properties of all LLVM-IR instruction are carried over into gMIR
  (see upstreams `MachineInstr::copyFlagsFromInstruction`).
-/

/-! # Lowering Patterns -/

/--
  gMIR 1:1 lowerings with Puddle for binary integer operations.

  This mirrors ArithToLLVM's lower1to1.
-/
def lower1to1 (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  let info := gOp.genericOpInfo
  Puddle.Pattern.Builder
    (do
      let root ← Puddle.MatchProg.root (.llvm lOp) #[] #[]
      let operands ← Puddle.MatchProg.operands root.op info.inOperandList.size
      let returnTypes ← Puddle.MatchProg.resultTypes root.op info.outOperandList.size
      return (returnTypes, operands, root))
    (fun (returnTypes, operands, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) operands returnTypes props
      return newOp)
    (fun newOp => newOp)

def g_add_pattern := lower1to1 .add .g_add

def g_sub_pattern := lower1to1 .sub .g_sub

def g_icmp_pattern := lower1to1 .icmp  .g_icmp

def g_add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite g_add_pattern.compile rewriter op opInBounds

def g_sub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite g_sub_pattern.compile rewriter op opInBounds

def g_icmp (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite g_icmp_pattern.compile rewriter op opInBounds

/-! # Pass implementation -/

def LLVMToGMIRPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    g_add, g_sub, g_icmp
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying llvm-to-gmir translation"
  | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Translate llvm dialect operations to gmir generic instructions."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
