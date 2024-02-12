import ERT.Utils.Wk
import Mathlib.Data.Fin.Tuple.Basic
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

def Ctx.den_in {τ} [CoeSort τ Type] (M: Type -> Type) (Γ: Ctx τ): Type
  := (k: Fin Γ.length) -> M ((Γ.get k).den_in M)

def Ctx.prod_den_in {τ} [CoeSort τ Type] (M: Type -> Type) (Γ: Ctx τ): Type
  := (k: Fin Γ.length) -> ((Γ.get k).den_in M)

def Ctx.pure_den_in {τ} [CoeSort τ Type] {M: Type -> Type} [Pure M] {Γ: Ctx τ}
  (G: Γ.prod_den_in M): Γ.den_in M
  := λk => pure (G k)

class TypedConst (α: Type) :=
  (Base: Type)
  (cnstTy: α -> Ty Base)

class Semantic (τ: Type)
  extends CoeSort τ Type where
  Effect: Type -> Type
  isMonad: Monad Effect
  isLawful: LawfulMonad Effect
  abort: (β: Type) -> Effect β

class SemanticConst (α: Type)
  extends TypedConst α, Semantic Base where
  cnstDen: (a: α) -> Effect ((cnstTy a).den_in Effect)

instance {τ} [Semantic τ]: Monad (Semantic.Effect τ)
  := Semantic.isMonad

instance {τ} [Semantic τ]: LawfulMonad (Semantic.Effect τ)
  := Semantic.isLawful

def Ty.den {τ} [e: Semantic τ]: Ty τ -> Type
  := Ty.den_in e.Effect

abbrev Ctx.den {τ} [e: Semantic τ]: Ctx τ -> Type
  := Ctx.den_in e.Effect

abbrev Ctx.prod_den {τ} [e: Semantic τ]: Ctx τ -> Type
  := Ctx.prod_den_in e.Effect

abbrev Ctx.pure_den {τ} [Semantic τ]: {Γ: Ctx τ}
  -> Γ.prod_den -> Γ.den
  := Ctx.pure_den_in

end Stlc

open Stlc

def WkList.den {τ} [Semantic τ] {Γ Δ: Ctx τ} (R: WkList ρ Γ Δ)
  (G: Γ.den): Δ.den
  := λk => (R.get_eq k) ▸ G (R.toWkNat.app k)

def WkList.den_lift {τ} [e: Semantic τ] {Γ Δ: Ctx τ} {A: Ty τ}
  (R: WkList ρ Γ Δ) (G: Γ.den) (x: e.Effect A.den)
  : (R.lift _).den (Fin.cons x G) = Fin.cons x (R.den G)
  := by funext ⟨k, Hk⟩; cases k <;> rfl

-- def WkList.den_lift' {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
--   (R: WkList ρ Γ Δ)
--   (R': WkList (liftWk ρ) (A::Γ) (A::Δ))
--   (G: Γ.den) (x: τ.Effect A.den)
--   : R'.den (Fin.cons x G) = Fin.cons x (R.den G)
--   := by funext ⟨k, Hk⟩; cases k <;> rfl

def WkList.den_step {τ} [e: Semantic τ] {Γ Δ: Ctx τ} {A: Ty τ}
  (R: WkList ρ Γ Δ) (G: Γ.den) (x: e.Effect A.den)
  : (R.step _).den (Fin.cons x G) = R.den G
  := by funext ⟨k, Hk⟩; rfl

def WkList.den_wk1 {τ} [e: Semantic τ] {Γ: Ctx τ} {A: Ty τ}
  (G: Γ.den) (x: e.Effect A.den)
  : (WkList.wk1 A Γ).den (Fin.cons x G) = G
  := by funext ⟨k, Hk⟩; rfl
