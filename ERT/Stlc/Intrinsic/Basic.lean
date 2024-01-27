import ERT.Stlc.Basic

--  TODO: study conversion between let2 and π?

--  TODO: Lean VSCode extension doesn't work when workspace root is not project root, for
-- `ERTLeanTogether`. Investigate, someday...

namespace Stlc.Intrinsic

inductive Var: Ctx -> Ty -> Type
| head: Var (A :: Γ) A
| tail: Var Γ A -> Var (B :: Γ) A

inductive Stlc: Ctx -> Ty -> Type
| var: Var Γ A -> Stlc Γ A
| app: Stlc Γ (Ty.fn A B) -> Stlc Γ A -> Stlc Γ B
| lam: Stlc (A :: Γ) B -> Stlc Γ (Ty.fn A B)
| pair: Stlc Γ A -> Stlc Γ B -> Stlc Γ (Ty.prod A B)
| let2: Stlc Γ (Ty.prod A B) -> Stlc (A :: B :: Γ) C -> Stlc Γ C
| cases: Stlc Γ (Ty.coprod A B) -> Stlc (A :: Γ) C -> Stlc (B :: Γ) C -> Stlc Γ C
| inl: Stlc Γ A -> Stlc Γ (Ty.coprod A B)
| inr: Stlc Γ B -> Stlc Γ (Ty.coprod A B)
| unit: Stlc Γ Ty.unit
| zero: Stlc Γ Ty.nat
| succ: Stlc Γ Ty.nat -> Stlc Γ Ty.nat
| natrec: Stlc Γ Ty.nat -> Stlc Γ C -> Stlc (C :: Γ) C -> Stlc Γ C
| abort: Stlc Γ A

inductive Wk: Ctx -> Ctx -> Type
| id: Wk [] []
| lift: Wk Γ Δ -> Wk (A :: Γ) (A :: Δ)
| step: Wk Γ Δ -> Wk (A :: Γ) Δ

open Wk

def Var.wk: Wk Γ Δ -> Var Δ A -> Var Γ A
| lift ρ, head => head
| lift ρ, tail v
| step ρ, v => tail (v.wk ρ)

def Stlc.wk (ρ: Wk Γ Δ): Stlc Δ A -> Stlc Γ A
| var v => var (v.wk ρ)
| app s t => app (s.wk ρ) (t.wk ρ)
| lam s => lam (s.wk ρ.lift)
| pair s t => pair (s.wk ρ) (t.wk ρ)
| let2 s t => let2 (s.wk ρ) (t.wk ρ.lift.lift)
| cases s t u => cases (s.wk ρ) (t.wk ρ.lift) (u.wk ρ.lift)
| inl s => inl (s.wk ρ)
| inr s => inr (s.wk ρ)
| unit => unit
| zero => zero
| succ s => succ (s.wk ρ)
| natrec n s z => natrec (n.wk ρ) (s.wk ρ) (z.wk ρ.lift)
| abort => abort

--  TODO: Subst
