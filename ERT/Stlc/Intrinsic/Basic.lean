import ERT.Stlc.Basic

--  TODO: study conversion between let2 and π?

--  TODO: Lean VSCode extension doesn't work when workspace root is not project root, for
-- `ERTLeanTogether`. Investigate, someday...

namespace Stlc.Intrinsic

inductive Var {τ}: Ctx τ -> Ty τ -> Type
| head: Var (A :: Γ) A
| tail: Var Γ A -> Var (B :: Γ) A

inductive Term {α} [τ: TypedConst α]: Ctx τ.Base -> Ty τ.Base -> Type
| var: Var Γ A -> Term Γ A
| app: Term Γ (Ty.fn A B) -> Term Γ A -> Term Γ B
| lam: Term (A :: Γ) B -> Term Γ (Ty.fn A B)
| pair: Term Γ A -> Term Γ B -> Term Γ (Ty.prod A B)
| let2: Term Γ (Ty.prod A B) -> Term (A :: B :: Γ) C -> Term Γ C
| cases: Term Γ (Ty.coprod A B) -> Term (A :: Γ) C -> Term (B :: Γ) C -> Term Γ C
| inl: Term Γ A -> Term Γ (Ty.coprod A B)
| inr: Term Γ B -> Term Γ (Ty.coprod A B)
| const (a: α): Term Γ (τ.cnstTy a)
| abort: Term Γ A

--TODO: factor to Wk utils as `WkList` or somesuch?
inductive Wk {τ}: Ctx τ -> Ctx τ -> Type
| id: Wk [] []
| lift: Wk Γ Δ -> Wk (A :: Γ) (A :: Δ)
| step: Wk Γ Δ -> Wk (A :: Γ) Δ

open Wk

def Var.wk: Wk Γ Δ -> Var Δ A -> Var Γ A
| lift ρ, head => head
| lift ρ, tail v
| step ρ, v => tail (v.wk ρ)

def Term.wk {α} [τ: TypedConst α] {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
  (ρ: Wk Γ Δ): Term Δ A -> Term Γ A
| var v => var (v.wk ρ)
| app s t => app (s.wk ρ) (t.wk ρ)
| lam s => lam (s.wk ρ.lift)
| pair s t => pair (s.wk ρ) (t.wk ρ)
| let2 s t => let2 (s.wk ρ) (t.wk ρ.lift.lift)
| cases s t u => cases (s.wk ρ) (t.wk ρ.lift) (u.wk ρ.lift)
| inl s => inl (s.wk ρ)
| inr s => inr (s.wk ρ)
| const a => const a
| abort => abort

--  TODO: Subst
