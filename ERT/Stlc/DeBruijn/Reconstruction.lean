import ERT.Stlc.DeBruijn.Basic
import ERT.Stlc.Intrinsic.Basic

namespace Stlc.DeBruijn

def HasTy.reconstruct {α} [TypedConst α] {Γ} {a: Term α} {A}
  : HasTy Γ a A -> Intrinsic.Term Γ A
  | HasTy.var x => Intrinsic.Term.var x.toIx
  | HasTy.app s t => Intrinsic.Term.app (reconstruct s) (reconstruct t)
  | HasTy.lam t => Intrinsic.Term.lam (reconstruct t)
  | HasTy.pair s t => Intrinsic.Term.pair (reconstruct s) (reconstruct t)
  | let1 s t => Intrinsic.Term.let1 (reconstruct s) (reconstruct t)
  | let2 s t => Intrinsic.Term.let2 (reconstruct s) (reconstruct t)
  | case e l r => Intrinsic.Term.case (reconstruct e) (reconstruct l) (reconstruct r)
  | inl s => Intrinsic.Term.inl (reconstruct s)
  | inr s => Intrinsic.Term.inr (reconstruct s)
  | cnst c => Intrinsic.Term.cnst c
  | abort A => Intrinsic.Term.abort A
