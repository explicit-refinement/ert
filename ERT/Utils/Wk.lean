import Mathlib.Order.Monotone.Basic
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic

/-!
# Weakenings

Definitions and utilities for weakening de-Bruijn indices
-/

def stepWk (ρ: Nat -> Nat): Nat -> Nat
  | n => (ρ n) + 1

def liftWk (ρ: Nat -> Nat): Nat -> Nat
  | 0 => 0
  | n + 1 => (ρ n) + 1

def liftWk_id: liftWk id = id := by funext n; cases n <;> simp [liftWk]

def liftWk_comp (ρ σ: Nat -> Nat): liftWk (ρ ∘ σ) = liftWk ρ ∘ liftWk σ := by
 funext n; cases n <;> simp [liftWk]

def liftWk_comp_succ (ρ: Nat -> Nat): liftWk ρ ∘ Nat.succ = Nat.succ ∘ ρ := by
  funext n; cases n <;> rfl

/-
Equality functions up-to-n
-/

def EqToN {α} (n: Nat) (ρ τ: Nat -> α): Prop :=
  ∀ m, m < n -> ρ m = τ m

theorem EqToN.zero {α}: EqToN 0 = (λ_ _: Nat -> α => True) := by
  funext ρ τ
  simp only [eq_iff_iff, iff_true]
  intro m H;
  cases H

theorem EqToN.zero_app {α} (ρ τ: Nat -> α): EqToN 0 ρ τ := by rw [EqToN.zero]; simp

theorem EqToN.succ_app {α} (n) (ρ τ: Nat -> α)
  : EqToN (n.succ) ρ τ ↔ (ρ n = τ n ∧ EqToN n ρ τ) := ⟨
  λH => ⟨H n (Nat.le_refl _), λm Hm => H m (Nat.le.step Hm)⟩,
  λ⟨Hn, H⟩ m Hm => match Hm with | Nat.le.refl => Hn | Nat.le.step Hm => H m Hm
⟩

theorem EqToN.le_sub {α} {n k} (Hnk: n ≤ k): Subrelation (@EqToN α k) (@EqToN α n)
  := λH m Hm => H m (Nat.le_trans Hm Hnk)

theorem EqToN.lt_sub {α} {n k} (Hnk: n < k): Subrelation (@EqToN α k) (@EqToN α n)
  := le_sub (Nat.le_of_lt Hnk)
theorem EqToN.succ_sub {α} (n): Subrelation (@EqToN α n.succ) (@EqToN α n)
  := le_sub (Nat.le_succ n)
theorem EqToN.pred_sub {α} (n): Subrelation (@EqToN α n) (@EqToN α n.pred)
  := le_sub (Nat.pred_le n)

theorem EqToN.refl {α} (n) (ρ: ℕ -> α): EqToN n ρ ρ := λ_ _ => rfl
theorem EqToN.symm {α} {n} {ρ τ: ℕ -> α} (H: EqToN n ρ τ): EqToN n τ ρ
  := λm Hm => (H m Hm).symm
theorem EqToN.trans {α} {n} {ρ τ σ: ℕ -> α} (H: EqToN n ρ τ) (H': EqToN n τ σ): EqToN n ρ σ
  := λm Hm => (H m Hm).trans (H' m Hm)

theorem EqToN.equivalence {α} (n): Equivalence (@EqToN α n) where
  refl _ _ _ := rfl
  symm := EqToN.symm
  trans := EqToN.trans

theorem EqToN.max_left {α n m}: Subrelation (@EqToN α (n.max m)) (@EqToN α n)
  := le_sub (Nat.le_max_left _ _)
theorem EqToN.max_right {α} {n m: ℕ}: Subrelation (@EqToN α (n.max m)) (@EqToN α m)
  := le_sub (Nat.le_max_right _ _)

def comp_congr_eqToN {α β n ρ τ} (f: α -> β): EqToN n ρ τ -> EqToN n (f ∘ ρ) (f ∘ τ)
  := λH m Hm => congrArg f (H m Hm)

def stepWk_congr_eqToN {n ρ τ}: EqToN n ρ τ -> EqToN n (stepWk ρ) (stepWk τ)
  := comp_congr_eqToN Nat.succ

def liftWk_eqToN_succ {n ρ τ}: EqToN n ρ τ -> EqToN n.succ (liftWk ρ) (liftWk τ)
  | _, 0, _ => rfl
  | H, m + 1, Hm => congrArg Nat.succ (H m (Nat.lt_succ.mp Hm))

def liftWk_congr_eqToN {n ρ τ}: EqToN n ρ τ -> EqToN n (liftWk ρ) (liftWk τ)
  | H => EqToN.succ_sub n (liftWk_eqToN_succ H)

def liftWk_eqToN_pred {n ρ τ}: EqToN n.pred ρ τ -> EqToN n (liftWk ρ) (liftWk τ)
  := match n with
  | 0 => liftWk_congr_eqToN
  | _ + 1 => liftWk_eqToN_succ

def liftWk_iter_eqToN_add {n ρ τ}
  : (m: Nat) -> EqToN n ρ τ -> EqToN (n + m) (liftWk^[m] ρ) (liftWk^[m] τ)
  | 0, H => H
  | m + 1, H => Function.iterate_succ' _ _ ▸ liftWk_eqToN_succ (liftWk_iter_eqToN_add m H)

/-
Nicer/more efficient definitions for iterated stepping
-/

abbrev wk1 := liftWk (Nat.succ)

def wknth (n: Nat): Nat -> Nat
  | m => if m < n then m else m + 1

def wknth_zero: wknth 0 = Nat.succ := rfl
def wknth_succ (n): wknth (n.succ) = liftWk (wknth n) := by
  funext m
  cases m with
  | zero => simp [wknth, liftWk]
  | succ m =>
    simp only [wknth, liftWk, Nat.succ_lt_succ_iff]
    split <;> rfl
def wknth_one: wknth 1 = wk1 := by rw [wknth_succ, wknth_zero, wk1]

def wknth_n (n): wknth n = liftWk^[n] Nat.succ := by
  induction n with
  | zero => rfl
  | succ n I => rw [wknth_succ, I, Function.iterate_succ']; rfl

def stepnWk (n: Nat) (ρ: Nat -> Nat): Nat -> Nat
  | m => (ρ m) + n

theorem stepnWk_zero: stepnWk 0 = id := rfl

theorem stepnWk_succ' (n): stepnWk (n.succ) = stepWk ∘ stepnWk n := by
  induction n with
  | zero => rfl
  | succ n I =>
    rw [I]
    funext ρ m
    simp_arith [stepWk, stepnWk]

theorem stepnWk_eq_iterate_stepWk: stepnWk = Nat.iterate stepWk := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => rw [stepnWk_succ', I, Function.iterate_succ']

theorem stepnWk_succ (n): stepnWk (n.succ) = stepnWk n ∘ stepWk := by
  rw [stepnWk_eq_iterate_stepWk, Function.iterate_succ]

def liftnWk (n: Nat) (ρ: Nat -> Nat): Nat -> Nat
  | m => if m < n then m else (ρ (m - n)) + n

theorem liftnWk_zero: liftnWk 0 = id := by
  funext ρ m
  simp only [liftnWk, Nat.sub_zero, Nat.add_zero, id_eq, ite_eq_right_iff]
  intro H
  cases H

theorem liftnWk_succ' (n): liftnWk (n.succ) = liftWk ∘ liftnWk n := by
  induction n with
  | zero => funext ρ m; cases m <;> rfl
  | succ n I =>
    rw [I]
    funext ρ m
    cases m with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => simp only [liftnWk, Nat.succ_lt_succ_iff, Nat.zero_lt_succ]; rfl
      | succ m =>
        simp only [liftnWk, Nat.succ_lt_succ_iff, Function.comp_apply, liftWk]
        split <;> simp_arith

theorem liftnWk_eq_iterate_liftWk: liftnWk = Nat.iterate liftWk := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => rw [liftnWk_succ', I, Function.iterate_succ']

theorem liftnWk_succ (n): liftnWk (n.succ) = liftnWk n ∘ liftWk := by
  rw [liftnWk_eq_iterate_liftWk, Function.iterate_succ]
