module

public import Veir.Pass
import Veir.Passes.Matching
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/-!
  # LLVMToGMIR pass

  This file replicates LLVM's GlobalISel IRTranslator pass.

  The all properties on LLVM-IR operations are carried over into gMIR
  (similar to upstreams `MachineInstr::copyFlagsFromInstruction`).

  This pass from LLVM IR to gMIR differs from the upstream implementation in the following notable ways:
  - Upstream converts all poison values to undef values; we only have poison but no undef.
  - Some informations that we represent as operation properties (e.g. the icmp condition code) are
    represented as special operands in upstream gMIR.
-/

/-! # Lowering Patterns -/

/--
  gMIR 1:1 lowerings with Puddle for binary operations.

  This should mirror ArithToLLVM's lower1to1. To support variable arity, we would need a Puddle equivalent
  of `pdl.results` and `pdl.operands`.
-/
def lowerBinop (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let lhsType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let rhsType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let lhs ← Puddle.MatchProg.value lhsType
      let rhs ← Puddle.MatchProg.value rhsType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[lhs, rhs] #[resultType]
      return (resultType, lhs, rhs, root))
    (fun (resultType, lhs, rhs, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[lhs, rhs] #[resultType] props
      return newOp)
    (fun newOp => newOp)

def g_add_pattern := lowerBinop .add .g_add

def g_sub_pattern := lowerBinop .sub .g_sub

def g_icmp_pattern := lowerBinop .icmp  .g_icmp

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
    description := "Lower llvm dialect operations to the gmir dialect."
    run := fun _ => LLVMToGMIRPass.impl }

end Veir
