module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

/-!
  # LLVMToGMIR pass

  Lowers every (not yet) operation of the `llvm` dialect into the `gMIR` dialect.
  This corresponds to LLVM's `IRTranslator` in GlobalISel (`llvm/CodeGen/GlobalISel/IRTranslator.h`).

  Currently, mostly copied code from ArithToLLVM.
-/

namespace Veir

/-! ## Generic 1:1 lowering -/

def lower1to1 (lOp : Llvm) (gOp : GMIR)
    (convert : propertiesOf (OpCode.llvm lOp) → propertiesOf (OpCode.gmir gOp)) (numOperands : Nat)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx.raw lOp numOperands
    | return rewriter
  let ip := InsertPoint.before op
  let (rewriter, newOp) ← rewriter.createOp! (.gmir gOp)
    (op.getResultTypes! rewriter.ctx.raw) operands #[] #[] (convert props) (some ip)
  let rewriter := rewriter.replaceValue! (op.getResult 0) (newOp.getResult 0)
  return rewriter.eraseOp! op

/-! ### The 1:1 patterns -/

def lowerAdd  := lower1to1 .add  .g_add  (fun p => p) 2
def lowerSub  := lower1to1 .sub  .g_sub  (fun p => p) 2
def lowerIcmp := lower1to1 .icmp .g_icmp (fun p => p) 2

/-! ## Pass implementation -/

def LLVMToGMIRPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    lowerAdd, lowerSub, lowerIcmp
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying llvm-to-gmir translation"
  | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Translate llvm dialect operations to gmir generic instructions."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
