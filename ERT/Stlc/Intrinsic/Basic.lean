import ERT.Stlc.Basic
import ERT.Utils.Wk

open ListWk

--  TODO: study conversion between let2 and π?

--  TODO: Lean VSCode extension doesn't work when workspace root is not project root, for
-- `ERTLeanTogether`. Investigate, someday...

namespace Stlc.Intrinsic

inductive Term {α} [τ: TypedConst α]: Ctx τ.Base -> Ty τ.Base -> Type
| var: Ix Γ A -> Term Γ A
| app: Term Γ (Ty.fn A B) -> Term Γ A -> Term Γ B
| lam: Term (A :: Γ) B -> Term Γ (Ty.fn A B)
| pair: Term Γ A -> Term Γ B -> Term Γ (Ty.prod A B)
| let1: Term Γ A -> Term (A :: Γ) B -> Term Γ B
| let2: Term Γ (Ty.prod A B) -> Term (A :: B :: Γ) C -> Term Γ C
| case: Term Γ (Ty.coprod A B) -> Term (A :: Γ) C -> Term (B :: Γ) C -> Term Γ C
| inl: Term Γ A -> Term Γ (Ty.coprod A B)
| inr: Term Γ B -> Term Γ (Ty.coprod A B)
| cnst (a: α): Term Γ (τ.cnstTy a)
| abort A: Term Γ A

def Term.wk {α} [τ: TypedConst α] {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
  (ρ: ListWk Γ Δ): Term Δ A -> Term Γ A
| var v => var (v.wk ρ)
| app s t => app (s.wk ρ) (t.wk ρ)
| lam s => lam (s.wk (ρ.lift _))
| pair s t => pair (s.wk ρ) (t.wk ρ)
| let1 s t => let1 (s.wk ρ) (t.wk (ρ.lift _))
| let2 s t => let2 (s.wk ρ) (t.wk ((ρ.lift _).lift _))
| case s t u => case (s.wk ρ) (t.wk (ρ.lift _)) (u.wk (ρ.lift _))
| inl s => inl (s.wk ρ)
| inr s => inr (s.wk ρ)
| cnst a => cnst a
| abort A => abort A

--  TODO: Subst
