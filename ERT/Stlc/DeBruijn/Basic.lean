import ERT.Stlc.Basic
import ERT.Utils.Wk

namespace Stlc.DeBruijn

inductive Stlc: Type
| var (n: Nat)
| app (s t: Stlc)
| lam (A: Ty) (t: Stlc)
| pair (s t: Stlc)
| let2 (s t: Stlc)
| cases (e l r: Stlc)
| inl (t: Stlc)
| inr (t: Stlc)
| nil
| zero
| succ (n: Stlc)
| natrec (n z s: Stlc)
| abort (A: Ty)

-- TODO: weakening

-- TODO: just make this a prop or smt...

inductive Var : Ctx -> Nat -> Ty -> Type
| head : Var (A :: Γ) 0 A
| tail : Var Γ n A -> Var (B :: Γ) (n + 1) A

-- TODO: HasTy

-- TODO: Subst

-- TODO: Iso w/ Intrinsic? In another file?
