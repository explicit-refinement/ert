import ERT.Stlc.DeBruijn2.Basic

namespace Stlc.DeBruijn2

def HasTy.den {Γ} {a: Term} {A} --[τ: Semantic BaseTy]
  : HasTy Γ a A -> Γ.den -> Option A.den
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
  | HasTy.zero, G => pure Nat.zero
  | HasTy.succ n, G => do
    let n <- n.den G
    pure (Nat.succ n)
  | HasTy.natrec z s n, G => do
    let z <- z.den G
    let n <- n.den G
    Nat.rec z (λi x => s.den (Fin.cons x (Fin.cons (pure i) G))) n
  | HasTy.abort _, _ => none--τ.abort _

def HasTy.den_cast {Γ: Ctx BaseTy} {a: Term} {A B}
  (H: HasTy Γ a A) (HAB : A = B)
  : den (HAB ▸ H) = HAB ▸ den H
  := by
    cases HAB
    rfl

def HasTy.den_cast_app {Γ: Ctx BaseTy} {a: Term} {A B}
  (H: HasTy Γ a A) (G: Γ.den) (HAB : A = B)
  : den (HAB ▸ H) G = HAB ▸ (den H G)
  := by
    cases HAB
    rfl

def HasTy.den_wk_app {ρ} {Γ Δ: Ctx BaseTy} {a: Term} {A}
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
  | HasTy.zero, G => rfl
  | HasTy.succ n, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R n G]
    rfl
  | HasTy.natrec z s n, G => by
    rw [HasTy.den, <-HasTy.den_wk_app R z G, <-HasTy.den_wk_app R n G, wk, HasTy.den]
    apply congrArg
    funext z
    apply congrArg
    funext n
    congr
    funext i x
    rw [HasTy.den_wk_app _ s _, WkList.den_lift2]
  | HasTy.abort _, _ => rfl

def HasTy.den_wk {ρ} {Γ Δ: Ctx BaseTy} {a: Term} {A}
  (R: WkList ρ Γ Δ) (H: HasTy Δ a A): (H.wk R).den = H.den ∘ R.den := by
  funext G; apply HasTy.den_wk_app

def Subst.Valid.den {σ} {Γ Δ: Ctx BaseTy}
  (V: Subst.Valid σ Γ Δ) (G: Γ.den): Δ.den
  := λk => (V k).den G

def Subst.Valid.lift_den {σ} {Γ Δ: Ctx BaseTy} {A: Ty BaseTy}
  (V: Subst.Valid σ Γ Δ) (G: Γ.den) (x: Option A.den)
  : (V.lift _).den (Fin.cons x G) = Fin.cons x (V.den G)
  := by funext ⟨k, Hk⟩; cases k with
  | zero => rfl
  | succ n => simp [den, lift, Fin.cons, HasTy.den_wk_app, WkList.den_wk1]


def Subst.Valid.lift2_den {σ} {Γ Δ: Ctx BaseTy} {A B: Ty BaseTy}
  (V: Subst.Valid σ Γ Δ) (G: Γ.den) (x: Option A.den) (y: Option B.den)
  : ((V.lift _).lift _).den (Fin.cons x (Fin.cons y G)) = Fin.cons x (Fin.cons y (V.den G))
  := by rw [lift_den, lift_den]

theorem HasTy.den_subst_app {σ} {Γ Δ: Ctx BaseTy} {a: Term} {A}
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
  | HasTy.zero, G => rfl
  | HasTy.succ n, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V n G]
    rfl
  | HasTy.natrec z s n, G => by
    rw [HasTy.den, <-HasTy.den_subst_app V z G, <-HasTy.den_subst_app V n G, subst, HasTy.den]
    apply congrArg
    funext z
    apply congrArg
    funext n
    congr
    funext i x
    rw [HasTy.den_subst_app _ s _, Subst.Valid.lift2_den]
  | HasTy.abort _, _ => rfl

theorem HasTy.den_subst {σ} {Γ Δ: Ctx BaseTy} {a: Term} {A}
  (V: Subst.Valid σ Γ Δ) (H: HasTy Δ a A): (H.subst V).den = H.den ∘ V.den := by
  funext G; apply HasTy.den_subst_app

def _root_.WkList.toSubst2 {ρ} {Γ Δ: Ctx BaseTy}
  (R: WkList ρ Γ Δ): Subst.Valid (Subst.fromWk ρ) Γ Δ
  := λk => R.get_eq k ▸ HasTy.var (R.toWkNat.app k)

theorem _root_.WkList.toSubst2_den {ρ} {Γ Δ: Ctx BaseTy}
  (R: WkList ρ Γ Δ) : R.toSubst2.den = R.den := by
  funext G ⟨k, Hk⟩
  simp [Subst.Valid.den, WkList.den, HasTy.den, WkList.toSubst2, HasTy.den_cast_app]

theorem HasTy.den_wk_toSubst2 {ρ}
  {Γ Δ: Ctx BaseTy} {a: Term} {A}
  (R: WkList ρ Γ Δ) (H: HasTy Δ a A): (H.wk R).den = (H.subst R.toSubst2).den := by
  rw [HasTy.den_wk, HasTy.den_subst, WkList.toSubst2_den]

def Subst.Valid.comp {ρ σ} {Γ Δ Ξ: Ctx BaseTy}
  (V: Subst.Valid ρ Γ Δ) (V': Subst.Valid σ Δ Ξ): Subst.Valid (ρ.comp σ) Γ Ξ
  := λk => (V' k).subst V

theorem Subst.Valid.den_comp {ρ σ} {Γ Δ Ξ: Ctx BaseTy}
  (V: Subst.Valid ρ Γ Δ) (V': Subst.Valid σ Δ Ξ) (G: Γ.den)
  : (V.comp V').den G = V'.den (V.den G) := by
  funext ⟨k, Hk⟩
  simp [Subst.Valid.den, Subst.Valid.comp, HasTy.den_subst_app]

theorem HasTy.subst0 {Γ: Ctx BaseTy} {a: Term} {A}
  (H: HasTy Γ a A)
  : Subst.Valid a.subst0 Γ (A::Γ)
  | ⟨0, _⟩ => H
  | ⟨n + 1, Hn⟩ => List.get_cons_succ.symm ▸ var ⟨n, Nat.lt_of_succ_lt_succ Hn⟩

theorem HasTy.alpha0 {Γ: Ctx BaseTy} {a: Term} {A B}
  (H: HasTy (A::Γ) a B)
  : Subst.Valid a.alpha0 (A::Γ) (B::Γ)
  | ⟨0, _⟩ => H
  | ⟨_ + 1, _⟩ => HasTy.var _
