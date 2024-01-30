import Mathlib.Data.Fin.Tuple.Basic

import ERT.Utils.Wk

namespace Abstract

class Syntax (α: Type u) where
  arity: α -> ℕ
  binding: (a: α) -> Fin (arity a) -> ℕ

instance initialSyntax: Syntax Empty where
  arity := λ_ => 0
  binding := λ.

instance treeSyntax: Syntax ℕ where
  arity := id
  binding := λ_ => 0

instance terminalSyntax: Syntax (List ℕ) where
  arity := List.length
  binding ℓ i := ℓ.get i

def Consts (α: Type u) := α

class ConstSyntax (α: Type u) extends Syntax α where
  zero_arity: ∀a: α, arity a = 0

instance constSyntax {α}: ConstSyntax (Consts α) where
  arity := λ_ => 0
  binding := λ_ _ => 0
  zero_arity _ := rfl

open Syntax

inductive Term (α: Type u) [Syntax α]: Type u
  | var (n: ℕ)
  | tm (a: α) (ts: Fin (arity a) -> Term α)

def Term.wk {α} [Syntax α] (ρ: ℕ -> ℕ): Term α -> Term α
  | var n => var (ρ n)
  | tm a ts => tm a (λ i => (ts i).wk (liftnWk (binding a i) ρ))

theorem Term.wk_id {α} [Syntax α]: (t: Term α) -> t.wk id = t
  | var n => rfl
  | tm a ts => by simp only [Term.wk, liftnWk_id, wk_id]

theorem Term.wk_id' {α} [Syntax α]: (t: Term α) -> t.wk (λx => x) = t
  := Term.wk_id

theorem Term.wk_comp {α} [Syntax α] (ρ σ: ℕ -> ℕ)
  : (t: Term α) -> t.wk (ρ ∘ σ) = (t.wk σ).wk ρ
  | var n => rfl
  | tm a ts => by simp only [Term.wk, liftnWk_comp, wk_comp]

def Term.fv {α} [Syntax α]: (t: Term α) -> ℕ
  | var n => n + 1
  | tm a ts => Fin.foldr (arity a) (λi v => Nat.max v ((ts i).fv - binding a i)) 0

def Subst (α: Type u) [Syntax α] := ℕ -> Term α

def Subst.id (α) [Syntax α]: Subst α := Term.var

def Subst.lift {α} [Syntax α] (σ: Subst α): Subst α
  | 0 => Term.var 0
  | n+1 => (σ n).wk Nat.succ

def Subst.liftn {α} [Syntax α] (n: ℕ) (σ: Subst α): Subst α
  | m => if m < n then Term.var m else (σ (m - n)).wk (λv => v + n)

def Subst.liftn_zero {α} [Syntax α] (σ: Subst α): σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).wk_id

def Subst.liftn_succ {α} [Syntax α] (n) (σ: Subst α)
  : σ.liftn n.succ = (σ.liftn n).lift := by
  induction n with
  | zero =>
    funext m
    simp only [lift]
    split
    . rfl
    . simp only [liftn]
      split
      . rename_i H; simp_arith at H
      . simp_arith [Term.wk_id']
  | succ n I =>
    funext m
    rw [I]
    simp only [lift]
    split
    . rfl
    . simp only [liftn]
      split
      . split
        . rfl
        . split
          . rfl
          . rename_i H C; exact (C (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ H))).elim
      . split
        . rename_i H; simp_arith at H
        . split
          . rename_i C H; exact (C (Nat.succ_lt_succ (Nat.succ_lt_succ H))).elim
          . simp only [<-Term.wk_comp]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

def Subst.liftn_eq_iterate_lift_apply {α} [Syntax α] (n: ℕ) (σ: Subst α)
  : σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n I => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]
def Subst.liftn_eq_iterate_lift (α) [Syntax α] (n: ℕ)
  : Subst.liftn n = (@Subst.lift α _)^[n] := by
  funext σ
  rw [liftn_eq_iterate_lift_apply]

def Subst.lift_zero {α} [Syntax α] (σ: Subst α): σ.lift 0 = Term.var 0 := rfl
def Subst.lift_succ {α} [Syntax α] (σ: Subst α) (n): (σ.lift n.succ) = (σ n).wk Nat.succ := rfl

def Subst.lift_id (α) [Syntax α]: (id α).lift = id α := by funext n; cases n <;> rfl

def Subst.iterate_lift_id (α) [Syntax α]: (n: ℕ) -> Subst.lift^[n] (id α) = id α
  | 0 => rfl
  | n + 1 => by simp [lift_id, iterate_lift_id α n]
def Subst.liftn_id (α) [Syntax α] (n: ℕ): (id α).liftn n = id α :=
  by rw [liftn_eq_iterate_lift_apply, iterate_lift_id]

def Subst.liftn_add (α) [Syntax α] (n m: ℕ)
  : Subst.liftn (m + n) = (@Subst.liftn α _ m) ∘ (@Subst.liftn α _ n)
  := by simp [liftn_eq_iterate_lift, Function.iterate_add]
def Subst.liftn_add_apply {α} [Syntax α] (n m: ℕ) (σ: Subst α): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

def Term.subst {α} [Syntax α] (σ: Subst α): Term α -> Term α
  | var n => σ n
  | tm a ts => tm a (λ i => (ts i).subst (σ.liftn (binding a i)))

def Term.subst_id {α} [Syntax α]: (t: Term α) -> t.subst (Subst.id α) = t
  | var n => rfl
  | tm a ts => by simp only [Term.subst, Subst.liftn_id, Term.subst_id]

def Subst.fromWk (α) [Syntax α] (ρ: ℕ -> ℕ): Subst α := Term.var ∘ ρ

theorem Subst.fromWk_lift (α) [Syntax α] (ρ): (fromWk α ρ).lift = fromWk α (liftWk ρ) := by
  funext n; cases n <;> rfl

theorem Subst.fromWk_iterate_lift (α) [Syntax α]:
  (n: ℕ) -> ∀ρ, Subst.lift^[n] (fromWk α ρ) = fromWk α (liftWk^[n] ρ)
  | 0, ρ => rfl
  | n + 1, ρ => by simp [fromWk_lift, fromWk_iterate_lift α n]
theorem Subst.fromWk_liftn (α) [Syntax α] (n ρ): (fromWk α ρ).liftn n = fromWk α (liftnWk n ρ) := by
  rw [liftn_eq_iterate_lift, liftnWk_eq_iterate_liftWk, fromWk_iterate_lift]

theorem Term.subst_wk {α} [Syntax α] (ρ: ℕ -> ℕ)
  : (t: Term α) -> t.subst (Subst.fromWk α ρ) = t.wk ρ
  | var n => rfl
  | tm a ts => by simp only [Term.subst, Term.wk, Subst.fromWk_liftn, subst_wk]

theorem Term.subst_liftn {α} [Syntax α] (n: ℕ) (σ: Subst α)
  :  (t: Term α) ->
    (t.wk (liftnWk n Nat.succ)).subst (σ.liftn (n + 1))
    = (t.subst (σ.liftn n)).wk (liftnWk n Nat.succ)
  | var n => by
    --TODO: how should this be factored?
    simp only [wk, subst, liftnWk, Subst.liftn]
    split
    . split
      . simp [wk, liftnWk, *]
      . rename_i H C; exact (C (Nat.le_step H)).elim
    . rename_i C
      simp_arith only [ite_false, <-wk_comp]
      apply congr
      . apply congrArg
        funext v
        simp_arith [Function.comp_apply, Zero.zero, liftnWk]
      . simp [Nat.succ_add, Nat.succ_sub_succ, Nat.add_sub_assoc]
  | tm a ts => by
    simp only [subst, wk, <-liftnWk_add_apply, Subst.liftn_add_apply]
    simp only [<-subst_liftn]
    rfl
theorem Term.subst_iterate_lift {α} [Syntax α] (n: ℕ) (σ: Subst α) (t: Term α)
  : (t.wk (liftWk^[n] Nat.succ)).subst (Subst.lift^[n + 1] σ)
    = (t.subst (Subst.lift^[n] σ)).wk (liftWk^[n] Nat.succ)
  := by simp only [<-Subst.liftn_eq_iterate_lift, <-liftnWk_eq_iterate_liftWk, subst_liftn]

theorem Term.subst_lift {α} [Syntax α] (t: Term α) (σ: Subst α)
  : (t.wk Nat.succ).subst (σ.lift) = (t.subst σ).wk Nat.succ := t.subst_iterate_lift 0 σ

def Subst.comp {α} [Syntax α] (σ τ: Subst α): Subst α
  | n => (τ n).subst σ

theorem Subst.lift_comp {α} [Syntax α] (σ τ: Subst α): (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [lift, comp, Term.subst_lift]

theorem Subst.iterate_lift_comp {α} [Syntax α]
  : (n: ℕ) -> ∀σ τ: Subst α, Subst.lift^[n] (σ.comp τ) = (Subst.lift^[n] σ).comp (Subst.lift^[n] τ)
  | 0, σ, τ => rfl
  | n + 1, σ, τ => by simp [Subst.lift_comp, iterate_lift_comp n]
theorem Subst.liftn_comp {α} [Syntax α] (n: ℕ) (σ τ: Subst α)
  : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by rw [liftn_eq_iterate_lift, iterate_lift_comp]

theorem Term.subst_comp {α} [Syntax α] (σ τ: Subst α)
  :  (t: Term α) -> t.subst (σ.comp τ) = (t.subst τ).subst σ
  | var n => rfl
  | tm a ts => by simp only [subst, Subst.liftn_comp, Term.subst_comp]

-- TODO: comp_id
-- TODO: comp_assoc
-- ==> Monoid (Subst α)
-- ==> monoid homomorphism {lift, liftn}

def Term.subst0 {α} [Syntax α] (t: Term α): Subst α
  | 0 => t
  | n + 1 => var n

def Term.alpha0 {α} [Syntax α] (t: Term α): Subst α
  | 0 => t
  | n => var n

--TODO: closed terms
--TODO: weakening, substitution do not affect closed terms

structure SyntaxHom (α: Type u) (β: Type v) [Syntax α] [Syntax β] where
  toFun: α -> β
  map_arity': ∀a: α, arity (toFun a) = arity a
  map_bindings': ∀a: α, ∀i: Fin (arity (toFun a)),
    binding (toFun a) i = binding a (map_arity' a ▸ i)

def SyntaxHom.id (α) [Syntax α]: SyntaxHom α α where
  toFun := _root_.id
  map_arity' := by simp
  map_bindings' := by simp

def SyntaxHom.comp {α β γ} [Syntax α] [Syntax β] [Syntax γ]
  (f: SyntaxHom β γ) (g: SyntaxHom α β): SyntaxHom α γ
  where
  toFun := f.toFun ∘ g.toFun
  map_arity' := by intros; simp only [map_arity', Function.comp_apply]
  map_bindings' := by intros; simp [map_bindings', Function.comp_apply, Eq.rec_eq_cast]

theorem SyntaxHom.ext {α β} [Syntax α] [Syntax β]
  {f g: SyntaxHom α β}
  (h: ∀a: α, f.toFun a = g.toFun a)
  : f = g := by
  cases f; cases g
  simp only [SyntaxHom.mk.injEq]
  apply funext
  exact h

theorem SyntaxHom.comp_id {α β} [Syntax α] [Syntax β] (f: SyntaxHom α β)
  : f.comp (SyntaxHom.id α) = f := SyntaxHom.ext (by simp [id, comp])

theorem SyntaxHom.id_comp {α β} [Syntax α] [Syntax β] (f: SyntaxHom α β)
  : (SyntaxHom.id β).comp f = f := SyntaxHom.ext (by simp [id, comp])

theorem SyntaxHom.comp_assoc {α β γ δ} [Syntax α] [Syntax β] [Syntax γ] [Syntax δ]
  (f: SyntaxHom α β) (g: SyntaxHom β γ) (h: SyntaxHom γ δ)
  : (h.comp g).comp f = h.comp (g.comp f) := SyntaxHom.ext (by simp [comp])

-- TODO: category of syntax homs
-- TODO: initial object
-- TODO: is List ℕ the terminal object?
-- TODO: coproducts?
-- TODO: products? tensor products? other limits?

class SyntaxHomClass (F) (α β: outParam (_)) [Syntax α] [Syntax β]
  extends DFunLike F α (λ_ => β) where
  map_arity: ∀f: F, ∀a: α, arity (f a) = arity a
  map_bindings: ∀f: F, ∀a: α, ∀i: Fin (arity (f a)),
    binding (f a) i = binding a (map_arity f a ▸ i)

open SyntaxHomClass

instance SyntaxHom.SyntaxHomClass {α β} [Syntax α] [Syntax β]: SyntaxHomClass (SyntaxHom α β) α β
  where
  coe := SyntaxHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_arity := SyntaxHom.map_arity'
  map_bindings := SyntaxHom.map_bindings'

def Term.relabel {F α β} [Syntax α] [Syntax β] [SyntaxHomClass F α β] (f: F)
  : Term α -> Term β
  | var n => var n
  | tm a ts => tm (f a) (λ i => (ts (map_arity f a ▸ i)).relabel f)

--TODO: relabeling preserves free variables, in part. maps closed terms to closed terms
--TODO: relabeling is functorial
