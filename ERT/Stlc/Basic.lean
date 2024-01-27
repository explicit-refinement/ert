namespace Stlc

inductive Ty (τ: Type)
  | base (X: τ)
  | prod (A B: Ty τ)
  | coprod (A B: Ty τ)
  | fn (A B: Ty τ)

--TODO: functor, monad, etc...
def Ty.map {τ τ'} (f: τ -> τ'): Ty τ -> Ty τ'
  | base X => base (f X)
  | prod A B => prod (A.map f) (B.map f)
  | coprod A B => coprod (A.map f) (B.map f)
  | fn A B => fn (A.map f) (B.map f)

def Ctx (τ: Type) := List (Ty τ)

def Ty.den {τ} [CoeSort τ Type] (M: Type -> Type): Ty τ -> Type
  | base t => t
  | prod A B => (A.den M) × (B.den M)
  | coprod A B => (A.den M) ⊕ (B.den M)
  | fn A B => (A.den M) -> M (B.den M)

def Ctx.den {τ} [CoeSort τ Type] (M: Type -> Type): Ctx τ -> Type
  | [] => Unit
  | A::Γ => M (A.den M) × (den M Γ)

def Ctx.prod_den {τ} [CoeSort τ Type] (M: Type -> Type): Ctx τ -> Type
  | [] => Unit
  | A::Γ => (A.den M) × (prod_den M Γ)

def Ctx.pure_den {τ} [CoeSort τ Type] {M: Type -> Type} [Pure M]: {Γ: Ctx τ}
  -> Γ.prod_den M -> Γ.den M
  | [], _ => ()
  | _::_, γ' => (pure γ'.1, pure_den γ'.2)

class TypedConst (α: Type) :=
  (Base: Type)
  (cnstTy: α -> Ty Base)
