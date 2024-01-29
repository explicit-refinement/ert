import ERT.Stlc.DeBruijn.Syntax
import ERT.Utils.Wk

namespace Stlc.DeBruijn

-- TODO: just make this a prop or smt...

inductive Var {τ}: Ctx τ -> Nat -> Ty τ -> Type
| head : Var (A :: Γ) 0 A
| tail : Var Γ n A -> Var (B :: Γ) (n + 1) A

open Term
open Ty

inductive HasTy {α} [τ: TypedConst α]: Ctx τ.Base -> Term α -> Ty τ.Base -> Type
| var : Var Γ n A -> HasTy Γ (var n) A
| app : HasTy Γ s (fn A B)
    -> HasTy Γ t A
    -> HasTy Γ (app s t) B
| lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
| pair : HasTy Γ s A
    -> HasTy Γ t B
    -> HasTy Γ (pair s t) (prod A B)
| let2 : HasTy Γ s (prod A B)
    -> HasTy (A :: B :: Γ) t C
    -> HasTy Γ (let2 s t) C
| case : HasTy Γ s (coprod A B)
    -> HasTy (A :: Γ) t C
    -> HasTy (B :: Γ) u C
    -> HasTy Γ (case s t u) C
| inl : HasTy Γ s A -> HasTy Γ (inj 0 s) (coprod A B)
| inr : HasTy Γ s B -> HasTy Γ (inj 1 s) (coprod A B)
| cnst : HasTy Γ (cnst a) (τ.cnstTy a)
| abort : HasTy Γ (abort A) A

-- TODO: Subst
