namespace Stlc

inductive Ty
| unit
| nat
| prod (A B: Ty)
| coprod (A B: Ty)
| fn (A B: Ty)

def Ctx := List Ty

def Ty.den (M: Type -> Type): Ty -> Type
| unit => Unit
| nat => Nat
| prod A B => (A.den M) × (B.den M)
| coprod A B => (A.den M) ⊕ (B.den M)
| fn A B => (A.den M) -> M (B.den M)

def Ctx.den (M: Type -> Type): Ctx -> Type
| [] => Unit
| A::Γ => M (A.den M) × (den M Γ)

def Ctx.prod_den (M: Type -> Type): Ctx -> Type
| [] => Unit
| A::Γ => (A.den M) × (prod_den M Γ)

def Ctx.pure_den {M: Type -> Type} [Pure M]: {Γ: Ctx} -> Γ.prod_den M -> Γ.den M
| [], _ => ()
| _::_, γ' => (pure γ'.1, pure_den γ'.2)
