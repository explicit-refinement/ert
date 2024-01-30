import Mathlib.Data.Fin.Tuple.Basic

import ERT.Utils.Wk

namespace Abstract

class Syntax (α: Type u) where
  arity: α -> ℕ
  binding: (a: α) -> Fin (arity a) -> ℕ

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

def Subst.liftn_eq_iterate_lift {α} [Syntax α] (n: ℕ) (σ: Subst α)
  : σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n I => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

def Subst.lift_zero {α} [Syntax α] (σ: Subst α): σ.lift 0 = Term.var 0 := rfl
def Subst.lift_succ {α} [Syntax α] (σ: Subst α) (n): (σ.lift n.succ) = (σ n).wk Nat.succ := rfl

def Subst.lift_id (α) [Syntax α]: (id α).lift = id α := by funext n; cases n <;> rfl

def Subst.iterate_lift_id (α) [Syntax α]: (n: ℕ) -> Subst.lift^[n] (id α) = id α
  | 0 => rfl
  | n + 1 => by simp [lift_id, iterate_lift_id α n]
def Subst.liftn_id (α) [Syntax α] (n: ℕ): (id α).liftn n = id α :=
  by rw [liftn_eq_iterate_lift, iterate_lift_id]

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
