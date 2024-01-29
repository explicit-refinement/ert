import ERT.Stlc.DeBruijn.Syntax
import ERT.Utils.Wk

namespace Stlc.DeBruijn

open Term
open Ty

inductive HasTy {α} [τ: TypedConst α]: Ctx τ.Base -> Term α -> Ty τ.Base -> Type
| var : At Γ n A -> HasTy Γ (var n) A
| app : HasTy Γ s (fn A B)
    -> HasTy Γ t A
    -> HasTy Γ (app s t) B
| lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
| pair : HasTy Γ s A
    -> HasTy Γ t B
    -> HasTy Γ (pair s t) (prod A B)
| let1: HasTy Γ s A
    -> HasTy (A :: Γ) t B
    -> HasTy Γ (let1 s t) B
| let2 : HasTy Γ s (prod A B)
    -> HasTy (A :: B :: Γ) t C
    -> HasTy Γ (let2 s t) C
| case : HasTy Γ s (coprod A B)
    -> HasTy (A :: Γ) t C
    -> HasTy (B :: Γ) u C
    -> HasTy Γ (case s t u) C
| inl : HasTy Γ s A -> HasTy Γ (inj 0 s) (coprod A B)
| inr : HasTy Γ s B -> HasTy Γ (inj 1 s) (coprod A B)
| cnst a : HasTy Γ (cnst a) (τ.cnstTy a)
| abort A : HasTy Γ (abort A) A

def HasTy.wk {α} [τ: TypedConst α] {ρ} {Γ Δ: Ctx τ.Base} {t: Term α} {A: Ty τ.Base}
  (R: WkList ρ Γ Δ): HasTy Δ t A -> HasTy Γ (t.wk ρ) A
  | var v => var (v.wk R)
  | app s t => app (HasTy.wk R s) (HasTy.wk R t)
  | lam t => lam (HasTy.wk (WkList.lift _ R) t)
  | pair s t => pair (HasTy.wk R s) (HasTy.wk R t)
  | let1 s t => let1 (HasTy.wk R s) (HasTy.wk (WkList.lift _ R) t)
  | let2 s t => let2 (HasTy.wk R s) (HasTy.wk (WkList.lift _ (WkList.lift _ R)) t)
  | case s t u => case (HasTy.wk R s)
    (HasTy.wk (WkList.lift _ R) t)
    (HasTy.wk (WkList.lift _ R) u)
  | inl s => inl (HasTy.wk R s)
  | inr s => inr (HasTy.wk R s)
  | cnst a => cnst a
  | abort A => abort A

structure Subst.Valid {α} [τ: TypedConst α] (σ: Subst α) (Γ Δ: Ctx τ.Base) where
    var: ∀{n A}, At Δ n A -> HasTy Γ (σ n) A

def Subst.Valid.lift {α} [τ: TypedConst α] {σ: Subst α} {Γ Δ: Ctx τ.Base}
    (A: Ty τ.Base) (V: Subst.Valid σ Γ Δ): Subst.Valid σ.lift (A :: Γ) (A :: Δ)
    where
    var := λ{n} => match n with
    | 0 => λR => HasTy.var (R.head_eq ▸ At.head _ _)
    | _ + 1 => λR => (V.var R.to_tail).wk (WkList.wk1 _ _)

def HasTy.subst {α} [τ: TypedConst α] {σ} {Γ Δ: Ctx τ.Base} {t: Term α} {A: Ty τ.Base}
    (V: Subst.Valid σ Γ Δ): HasTy Δ t A -> HasTy Γ (t.subst σ) A
    | var v => V.var v
    | app s t => app (HasTy.subst V s) (HasTy.subst V t)
    | lam t => lam (HasTy.subst (V.lift _) t)
    | pair s t => pair (HasTy.subst V s) (HasTy.subst V t)
    | let1 s t => let1 (HasTy.subst V s) (HasTy.subst (V.lift _) t)
    | let2 s t => let2 (HasTy.subst V s) (HasTy.subst ((V.lift _).lift _) t)
    | case s t u => case (HasTy.subst V s)
        (HasTy.subst (V.lift _) t)
        (HasTy.subst (V.lift _) u)
    | inl s => inl (HasTy.subst V s)
    | inr s => inr (HasTy.subst V s)
    | cnst a => cnst a
    | abort A => abort A
