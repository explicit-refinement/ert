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

def Ty.den_in {τ} [CoeSort τ Type] (M: Type -> Type): Ty τ -> Type
  | base t => t
  | prod A B => (A.den_in M) × (B.den_in M)
  | coprod A B => (A.den_in M) ⊕ (B.den_in M)
  | fn A B => (A.den_in M) -> M (B.den_in M)

def Ctx.den_in {τ} [CoeSort τ Type] (M: Type -> Type): Ctx τ -> Type
  | [] => Unit
  | A::Γ => M (A.den_in M) × (den_in M Γ)

def Ctx.prod_den_in {τ} [CoeSort τ Type] (M: Type -> Type): Ctx τ -> Type
  | [] => Unit
  | A::Γ => (A.den_in M) × (prod_den_in M Γ)

def Ctx.pure_den_in {τ} [CoeSort τ Type] {M: Type -> Type} [Pure M]: {Γ: Ctx τ}
  -> Γ.prod_den_in M -> Γ.den_in M
  | [], _ => ()
  | _::_, γ' => (pure γ'.1, pure_den_in γ'.2)

class TypedConst (α: Type) :=
  (Base: Type)
  (cnstTy: α -> Ty Base)

class SemanticConst (α: Type)
  extends TypedConst α, CoeSort Base Type where
  Effect: Type -> Type
  isMonad: Monad Effect
  isLawful: LawfulMonad Effect
  cnstDen: (a: α) -> Effect ((cnstTy a).den_in Effect)
  abort: (β: Type) -> Effect β

instance {α} [SemanticConst α]: Monad (SemanticConst.Effect α)
  := SemanticConst.isMonad

instance {α} [SemanticConst α]: LawfulMonad (SemanticConst.Effect α)
  := SemanticConst.isLawful

def Ty.den {α} [τ: SemanticConst α]: Ty τ.Base -> Type
  := Ty.den_in τ.Effect

abbrev Ctx.den {α} [τ: SemanticConst α]: Ctx τ.Base -> Type
  := Ctx.den_in τ.Effect

abbrev Ctx.prod_den {α} [τ: SemanticConst α]: Ctx τ.Base -> Type
  := Ctx.prod_den_in τ.Effect

abbrev Ctx.pure_den {α} [τ: SemanticConst α]: {Γ: Ctx τ.Base}
  -> Γ.prod_den -> Γ.den
  := Ctx.pure_den_in
