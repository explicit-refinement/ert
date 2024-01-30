import ERT.Stlc.DeBruijn.Basic

open Stlc
open Stlc.DeBruijn

def At.den {α} [τ: SemanticConst α]
  : {Γ: Ctx τ.Base} -> {n: ℕ} -> {A: _} -> At Γ n A -> Γ.den -> τ.Effect A.den
  | _::_, 0, _, R, (x, _G) => R.head_eq ▸ x
  | _::_, _ + 1, _, R, (_x, G) => At.den (R.to_tail) G

def AtT.den {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {n: ℕ} {A: _}
  : AtT Γ n A -> Γ.den -> τ.Effect A.den
  | AtT.head _ _, (x, _G) => x
  | AtT.tail _ v, (_x, G) => AtT.den v G

theorem AtT.den_head {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {A x G}
  : (AtT.head A Γ).den (x, G) = x
  := rfl

def AtT.den_tail {α} [τ: SemanticConst α] {Γ: Ctx τ.Base}
  {A: Ty τ.Base} {n} {v: AtT Γ n A} {x} {G: Γ.den}
  : (AtT.tail A v).den (x, G) = v.den G
  := rfl

def At.den_eq_app {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {n: ℕ} {A: _}
  : (v: At Γ n A) -> (G: Γ.den) -> v.den G = v.toAtT.den G
  | At.head _ _, (_, _) => rfl
  | At.tail _ _, (_, _) => by rw [den, toAtT, AtT.den, den_eq_app]

def At.den_eq {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {n: ℕ} {A: _} (v: At Γ n A)
  : v.den = v.toAtT.den := by funext _; rw [At.den_eq_app]

def AtT.den_eq {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {n: ℕ} {A: _} (v: AtT Γ n A)
  : v.den = v.toAt.den := by rw [At.den_eq]; apply congrArg; apply Subsingleton.allEq

def WkListT.den {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base}
  : WkListT ρ Γ Δ -> Γ.den -> Δ.den
  | WkListT.nil _, G => G
  | WkListT.lift _ R, (x, G) => (x, R.den G)
  | WkListT.step _ R, (x, G) => R.den G

def WkList.den {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} (R: WkList ρ Γ Δ)
  : Γ.den -> Δ.den
  := R.toWkListT.den

def WkList.den_eq_app {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base}
  (R: WkList ρ Γ Δ) (G: Γ.den): R.den G = R.toWkListT.den G
  := rfl

def WkList.den_eq {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base}
  (R: WkList ρ Γ Δ): R.den = R.toWkListT.den
  := rfl

def AtT.den_wk_t_app {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {n: ℕ} {A: _}
  : (R: WkListT ρ Γ Δ) -> (v: AtT Δ n A)
    -> (G: Γ.den) -> (v.wk_t R).den G = v.den (R.den G)
  | WkListT.step _ R, v, (x, G) => by rw [WkListT.den, wk_t, den, den_wk_t_app R v G]
  | WkListT.lift _ R, AtT.head _ _, (x, G) => by rw [WkListT.den, den, wk_t, den]
  | WkListT.lift _ R, AtT.tail _ v, (x, G) => by
    rw [WkListT.den, den, wk_t, den, den_wk_t_app R v G]

def AtT.den_wk_t {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {n: ℕ} {A: _}
  (R: WkListT ρ Γ Δ) (v: AtT Δ n A): (v.wk_t R).den = v.den ∘ R.den
  := by funext _; apply den_wk_t_app

def At.den_wk {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {n: ℕ} {A: _}
  (R: WkList ρ Γ Δ) (v: At Δ n A): (v.wk R).den = v.den ∘ R.den := by
  rw [At.den_eq, At.den_eq, WkList.den_eq, <-AtT.den_wk_t]
  apply congrArg
  apply Subsingleton.allEq

def At.den_wk_app {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {n: ℕ} {A: _}
  (R: WkList ρ Γ Δ) (v: At Δ n A) (G: Γ.den): (v.wk R).den G = v.den (R.den G) :=
  congrFun (v.den_wk R) _

def At.den_wk_t {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {n: ℕ} {A: _}
  (R: WkListT ρ Γ Δ) (v: At Δ n A): (v.wk R.toWkList).den = v.den ∘ R.den := by
  rw [den_wk]
  apply congrArg
  rw [WkList.den_eq R.toWkList]
  apply congrArg
  apply Subsingleton.allEq

def At.den_wk_t_app {α} [τ: SemanticConst α] {Γ Δ: Ctx τ.Base} {n: ℕ} {A: _}
  (R: WkListT ρ Γ Δ) (v: At Δ n A) (G: Γ.den)
  : (v.wk R.toWkList).den G = v.den (R.den G) :=
  congrFun (v.den_wk_t R) _

namespace Stlc.DeBruijn

def HasTy.den {α} [τ: SemanticConst α] {Γ} {a: Term α} {A}
  : HasTy Γ a A -> Γ.den -> τ.Effect A.den
  | HasTy.var v, G => v.den G
  | HasTy.app s t, G => do
    let s <- s.den G
    let t <- t.den G
    s t
  | HasTy.lam t, G => pure (λx => t.den (pure x, G))
  | HasTy.pair s t, G => do
    let s <- s.den G
    let t <- t.den G
    pure (s, t)
  | HasTy.let1 s t, G => do
    let s <- s.den G
    t.den (pure s, G)
  | HasTy.let2 s t, G => do
    let (x, y) <- s.den G
    t.den (pure x, pure y, G)
  | HasTy.case e l r, G => do
    let e <- e.den G
    match e with
    | Sum.inl x => l.den (pure x, G)
    | Sum.inr y => r.den (pure y, G)
  | HasTy.inl t, G => do
    let t <- t.den G
    pure (Sum.inl t)
  | HasTy.inr t, G => do
    let t <- t.den G
    pure (Sum.inr t)
  | HasTy.cnst c, G => τ.cnstDen c
  | HasTy.abort _, _ => τ.abort _

def HasTy.den_wk_t_app {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkListT ρ Γ Δ): (H: HasTy Δ a A) ->
    (G: Γ.den) -> (H.wk R.toWkList).den G = H.den (R.den G)
  | HasTy.var v, G => v.den_wk_t_app R G
  | HasTy.app s t, G => by
    rw [HasTy.den, <-HasTy.den_wk_t_app R s G, <-HasTy.den_wk_t_app R t G]
    rfl
  | HasTy.lam t, G => by
    rw [HasTy.den, wk, HasTy.den]
    apply congrArg
    funext x
    rw [HasTy.den_wk_t_app, WkListT.den]
  | HasTy.pair s t, G => by
    rw [HasTy.den, <-HasTy.den_wk_t_app R s G, <-HasTy.den_wk_t_app R t G]
    rfl
  | HasTy.let1 s t, G => by
    rw [HasTy.den, wk, HasTy.den,
      <-HasTy.den_wk_t_app R s G]
    apply congrArg
    funext s
    rw [HasTy.den_wk_t_app _ t _, WkListT.den]
  | HasTy.let2 s t, G => by
    rw [HasTy.den, wk, HasTy.den,
      <-HasTy.den_wk_t_app R s G]
    apply congrArg
    funext ⟨x, y⟩
    simp only []
    rw [HasTy.den_wk_t_app _ t _, WkListT.den, WkListT.den]
  | HasTy.case e l r, G => by
    rw [HasTy.den, <-HasTy.den_wk_t_app R e G, wk, HasTy.den]
    apply congrArg
    funext e
    split
    . rw [HasTy.den_wk_t_app _ l _, WkListT.den]
    . rw [HasTy.den_wk_t_app _ r _, WkListT.den]
  | HasTy.inl t, G => by
    rw [HasTy.den, <-HasTy.den_wk_t_app R t G]
    rfl
  | HasTy.inr t, G => by
    rw [HasTy.den, <-HasTy.den_wk_t_app R t G]
    rfl
  | HasTy.cnst c, G => rfl
  | HasTy.abort _, _ => rfl

def HasTy.den_wk_t {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkListT ρ Γ Δ) (H: HasTy Δ a A): (H.wk R.toWkList).den = H.den ∘ R.den := by
  funext G; rw [den_wk_t_app]; rfl

def HasTy.den_wk_app {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkList ρ Γ Δ) (H: HasTy Δ a A) (G: Γ.den): (H.wk R).den G = H.den (R.den G) := by
  rw [den_wk_t_app R.toWkListT]
  rfl

def HasTy.den_wk {α} [τ: SemanticConst α] {ρ} {Γ Δ: Ctx τ.Base} {a: Term α} {A}
  (R: WkList ρ Γ Δ) (H: HasTy Δ a A): (H.wk R).den = H.den ∘ R.den := by
   funext G; rw [den_wk_app]; rfl
