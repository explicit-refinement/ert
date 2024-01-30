import ERT.Stlc.DeBruijn.Basic

open Stlc
open Stlc.DeBruijn

def WkList.den {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} (R: WkList ρ Γ Δ)
  (G: Γ.den): Δ.den
  := λk => (R.get_eq k) ▸ G (R.toWkNat.app k)

def WkList.den_lift {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
  (R: WkList ρ Γ Δ) (G: Γ.den) (x: τ.Effect A.den)
  : (R.lift _).den (Fin.cons x G) = Fin.cons x (R.den G)
  := by funext ⟨k, Hk⟩; cases k <;> rfl

-- def WkList.den_lift' {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
--   (R: WkList ρ Γ Δ)
--   (R': WkList (liftWk ρ) (A::Γ) (A::Δ))
--   (G: Γ.den) (x: τ.Effect A.den)
--   : R'.den (Fin.cons x G) = Fin.cons x (R.den G)
--   := by funext ⟨k, Hk⟩; cases k <;> rfl

def WkList.den_step {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
  (R: WkList ρ Γ Δ) (G: Γ.den) (x: τ.Effect A.den)
  : (R.step _).den (Fin.cons x G) = R.den G
  := by funext ⟨k, Hk⟩; rfl

def WkList.den_wk1 {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {A: Ty τ.Base}
  (G: Γ.den) (x: τ.Effect A.den)
  : (WkList.wk1 A Γ).den (Fin.cons x G) = G
  := by funext ⟨k, Hk⟩; rfl

namespace Stlc.DeBruijn

def HasTy.den {α} [τ: SemanticConst α] {Γ} {a: Term α} {A}
  : HasTy Γ a A -> Γ.den -> τ.Effect A.den
  | HasTy.var v, G => G v
  | HasTy.app s t, G => do
    let s <- s.den G
    let t <- t.den G
    s t
  | HasTy.lam t, G => pure (λx => t.den (Fin.cons (pure x) G))
  | HasTy.pair s t, G => do
    let s <- s.den G
    let t <- t.den G
    pure (s, t)
  | HasTy.let1 s t, G => do
    let s <- s.den G
    t.den (Fin.cons (pure s) G)
  | HasTy.let2 s t, G => do
    let (x, y) <- s.den G
    t.den (Fin.cons (pure x) (Fin.cons (pure y) G))
  | HasTy.case e l r, G => do
    let e <- e.den G
    match e with
    | Sum.inl x => l.den (Fin.cons (pure x) G)
    | Sum.inr y => r.den (Fin.cons (pure y) G)
  | HasTy.inl t, G => do
    let t <- t.den G
    pure (Sum.inl t)
  | HasTy.inr t, G => do
    let t <- t.den G
    pure (Sum.inr t)
  | HasTy.cnst c, G => τ.cnstDen c
  | HasTy.abort _, _ => τ.abort _

def HasTy.den_cast {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {a: Term α} {A B}
  (H: HasTy Γ a A) (HAB : A = B)
  : den (HAB ▸ H) = HAB ▸ den H
  := by
    cases HAB
    rfl

def HasTy.den_cast_app {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {a: Term α} {A B}
  (H: HasTy Γ a A) (G: Γ.den) (HAB : A = B)
  : den (HAB ▸ H) G = HAB ▸ (den H G)
  := by
    cases HAB
    rfl

def HasTy.den_wk_app {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkList ρ Γ Δ): (H: HasTy Δ a A) ->
    (G: Γ.den) -> (H.wk R).den G = H.den (R.den G)
  | HasTy.var v, G => by
    simp only [wk, den, WkList.den, den_cast_app]
  | HasTy.app s t, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R s G, <-HasTy.den_wk_app R t G]
    rfl
  | HasTy.lam t, G => by
    rw [HasTy.den, wk, HasTy.den]
    apply congrArg
    funext x
    rw [HasTy.den_wk_app, WkList.den_lift]
  | HasTy.pair s t, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R s G, <-HasTy.den_wk_app R t G]
    rfl
  | HasTy.let1 s t, G => by
    rw [HasTy.den, wk, HasTy.den,
      <-HasTy.den_wk_app R s G]
    apply congrArg
    funext s
    rw [HasTy.den_wk_app _ t _, WkList.den_lift]
  | HasTy.let2 s t, G => by
    rw [HasTy.den, wk, HasTy.den,
      <-HasTy.den_wk_app R s G]
    apply congrArg
    funext ⟨x, y⟩
    simp only []
    rw [HasTy.den_wk_app _ t _, <-WkList.den_lift, <-WkList.den_lift]
  | HasTy.case e l r, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R e G, wk, HasTy.den]
    apply congrArg
    funext e
    split
    . rw [HasTy.den_wk_app _ l _, WkList.den_lift]
    . rw [HasTy.den_wk_app _ r _, WkList.den_lift]
  | HasTy.inl t, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R t G]
    rfl
  | HasTy.inr t, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R t G]
    rfl
  | HasTy.cnst c, G => rfl
  | HasTy.abort _, _ => rfl

def HasTy.den_wk {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkList ρ Γ Δ) (H: HasTy Δ a A): (H.wk R).den = H.den ∘ R.den := by
  funext G; apply HasTy.den_wk_app

def Subst.Valid.den {α} [τ: SemanticConst α] {σ} {Γ Δ: Ctx τ.Base}
  (V: Subst.Valid σ Γ Δ) (G: Γ.den): Δ.den
  := λk => (V k).den G

def Subst.Valid.lift_den {α} [τ: SemanticConst α] {σ} {Γ Δ: Ctx τ.Base} {A: Ty τ.Base}
  (V: Subst.Valid σ Γ Δ) (G: Γ.den) (x: τ.Effect A.den)
  : (V.lift _).den (Fin.cons x G) = Fin.cons x (V.den G)
  := by funext ⟨k, Hk⟩; cases k with
  | zero => rfl
  | succ n => simp [den, lift, Fin.cons, HasTy.den_wk_app, WkList.den_wk1]

theorem HasTy.den_subst_app {α} [τ: SemanticConst α] {σ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (V: Subst.Valid σ Γ Δ): (H: HasTy Δ a A) ->
    (G: Γ.den) -> (H.subst V).den G = H.den (V.den G)
  | HasTy.var _, _ => rfl
  | HasTy.app s t, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V s G, <-HasTy.den_subst_app V t G]
    rfl
  | HasTy.lam t, G => by
    rw [HasTy.den, subst, HasTy.den]
    apply congrArg
    funext x
    rw [HasTy.den_subst_app, Subst.Valid.lift_den]
  | HasTy.pair s t, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V s G, <-HasTy.den_subst_app V t G]
    rfl
  | HasTy.let1 s t, G => by
    rw [HasTy.den, subst, HasTy.den,
      <-HasTy.den_subst_app V s G]
    apply congrArg
    funext s
    rw [HasTy.den_subst_app _ t _, Subst.Valid.lift_den]
  | HasTy.let2 s t, G => by
    rw [HasTy.den, subst, HasTy.den,
      <-HasTy.den_subst_app V s G]
    apply congrArg
    funext ⟨x, y⟩
    simp only []
    rw [HasTy.den_subst_app _ t _, <-Subst.Valid.lift_den, <-Subst.Valid.lift_den]
    rfl
  | HasTy.case e l r, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V e G, subst, HasTy.den]
    apply congrArg
    funext e
    split
    . rw [HasTy.den_subst_app _ l _, Subst.Valid.lift_den]
    . rw [HasTy.den_subst_app _ r _, Subst.Valid.lift_den]
  | HasTy.inl t, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V t G]
    rfl
  | HasTy.inr t, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V t G]
    rfl
  | HasTy.cnst c, G => rfl
  | HasTy.abort _, _ => rfl

theorem HasTy.den_subst {α} [τ: SemanticConst α] {σ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (V: Subst.Valid σ Γ Δ) (H: HasTy Δ a A): (H.subst V).den = H.den ∘ V.den := by
  funext G; apply HasTy.den_subst_app

def _root_.WkList.toSubst {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base}
  (R: WkList ρ Γ Δ): Subst.Valid (Subst.fromWk _ ρ) Γ Δ
  := λk => R.get_eq k ▸ HasTy.var (R.toWkNat.app k)

theorem _root_.WkList.toSubst_den {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base}
  (R: WkList ρ Γ Δ) : R.toSubst.den = R.den := by
  funext G ⟨k, Hk⟩
  simp [Subst.Valid.den, WkList.den, HasTy.den, WkList.toSubst, HasTy.den_cast_app]

theorem HasTy.den_wk_toSubst {α} [τ: SemanticConst α] {ρ}
  {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkList ρ Γ Δ) (H: HasTy Δ a A): (H.wk R).den = (H.subst R.toSubst).den := by
  rw [HasTy.den_wk, HasTy.den_subst, WkList.toSubst_den]
