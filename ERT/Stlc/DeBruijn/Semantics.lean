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

def At.den_eq_app {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {n: ℕ} {A: _}
  : (v: At Γ n A) -> (G: Γ.den) -> v.den G = v.toAtT.den G
  | At.head _ _, (_, _) => rfl
  | At.tail _ _, (_, _) => by rw [den, toAtT, AtT.den, den_eq_app]

def At.den_eq {α} [τ: SemanticConst α] {Γ: Ctx τ.Base} {n: ℕ} {A: _} (v: At Γ n A)
  : v.den = v.toAtT.den := by funext _; rw [At.den_eq_app]

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
