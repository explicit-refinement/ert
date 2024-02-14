import Mathlib.Order.Monotone.Basic
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Fin.Basic

/-!
# Weakenings

Definitions and utilities for weakening de-Bruijn indices
-/

def stepWk (ρ: Nat -> Nat): Nat -> Nat := Nat.succ ∘ ρ

def liftWk (ρ: Nat -> Nat): Nat -> Nat
  | 0 => 0
  | n + 1 => (ρ n) + 1

def liftWk_id: liftWk id = id := by funext n; cases n <;> simp [liftWk]

def liftWk_injective: Function.Injective liftWk := by
  intro ρ σ H
  funext n
  have H': liftWk ρ (n + 1) = liftWk σ (n + 1) := by rw [H]
  exact Nat.succ_injective H'

def stepWk_injective: Function.Injective stepWk := by
  intro ρ σ H
  funext n
  have H': stepWk ρ n = stepWk σ n := by rw [H]
  exact Nat.succ_injective H'

def liftWk_comp (ρ σ: Nat -> Nat): liftWk (ρ ∘ σ) = liftWk ρ ∘ liftWk σ := by
 funext n; cases n <;> rfl

def liftWk_comp_succ (ρ: Nat -> Nat): liftWk ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl

def liftWk_ne_stepWk (ρ σ: Nat -> Nat): liftWk ρ ≠ stepWk σ :=
  have H: (liftWk ρ 0) ≠ (stepWk σ 0) := by simp [liftWk, stepWk]
  λH' => H (by rw [H'])

/-
Finite lifts
-/

def stepFin {n m} (ρ: Fin n -> Fin m): Fin n -> Fin (m + 1)
  := Fin.succ ∘ ρ

def liftFin {n m} (ρ: Fin n -> Fin m): Fin (n + 1) -> Fin (m + 1)
  := Fin.cases 0 (Fin.succ ∘ ρ)

def liftFin_id (n): liftFin (@id (Fin n)) = id := by
  funext ⟨k, H⟩
  cases k with
  | zero => rfl
  | succ k => rfl

def liftFin_injective (n m): Function.Injective (@liftFin n m) := by
  intro ρ σ H
  funext k
  have H': liftFin ρ k.succ = liftFin σ k.succ := by rw [H]
  exact Fin.succ_injective _ H'

def liftFin_comp {n m} (ρ: Fin m -> Fin k) (σ: Fin n -> Fin m):
  liftFin (ρ ∘ σ) = liftFin ρ ∘ liftFin σ := by
  funext ⟨k, Hk⟩; cases k <;> rfl

def liftFin_comp_succ {n m} (ρ: Fin n -> Fin m): liftFin ρ ∘ Fin.succ = Fin.succ ∘ ρ := rfl

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

def liftWk_iterate_eqToN_add {n ρ τ}
  : (m: Nat) -> EqToN n ρ τ -> EqToN (n + m) (liftWk^[m] ρ) (liftWk^[m] τ)
  | 0, H => H
  | m + 1, H => Function.iterate_succ' _ _ ▸ liftWk_eqToN_succ (liftWk_iterate_eqToN_add m H)

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

theorem liftnWk_add (m n: ℕ): liftnWk (m + n) = liftnWk m ∘ liftnWk n
  := by rw [liftnWk_eq_iterate_liftWk, Function.iterate_add]
theorem liftnWk_add_apply (m n: ℕ) (ρ): liftnWk (m + n) ρ = liftnWk m (liftnWk n ρ)
  := by rw [liftnWk_eq_iterate_liftWk, Function.iterate_add_apply]

theorem iterate_liftWk_id: (n: ℕ) -> liftWk^[n] id = id
  | 0 => rfl
  | n + 1 => by simp [liftWk_id, iterate_liftWk_id n]
theorem iterate_liftWk_comp: (n: ℕ)
  -> ∀ρ σ, liftWk^[n] (ρ ∘ σ) = liftWk^[n] ρ ∘ liftWk^[n] σ
  | 0, _, _ => rfl
  | n + 1, _, _ => by simp [liftWk_comp, iterate_liftWk_comp n]

theorem liftnWk_id (n): liftnWk n id = id := by
  rw [liftnWk_eq_iterate_liftWk, iterate_liftWk_id]
theorem liftnWk_comp (n ρ σ): liftnWk n (ρ ∘ σ) = liftnWk n ρ ∘ liftnWk n σ := by
  rw [liftnWk_eq_iterate_liftWk, iterate_liftWk_comp]

def liftnWk_eqToN_add {n ρ τ} (m: Nat) (H: EqToN n ρ τ): EqToN (n + m) (liftnWk m ρ) (liftnWk m τ)
  := liftnWk_eq_iterate_liftWk ▸ liftWk_iterate_eqToN_add m H

/-
Nicer/more efficient definitions for iterated finite stepping
-/

def Fin.addCast {m: Nat} (i: Fin m) (n: Nat): Fin (n + m)
  := i.castLE (by simp)

def Fin.casesAdd {m n: Nat} {motive: Fin (m + n) -> Sort u}
  (left: ∀ i: Fin m, motive (addNat i n))
  (right: ∀ i: Fin n, motive (addCast i m))
  (i: Fin (m + n)): motive i
  := if hi : (i : Nat) < n then right (i.castLT hi)
  else Fin.addNat_subNat (Nat.le_of_not_lt hi) ▸ left (subNat n i (Nat.le_of_not_lt hi))

def Fin.sumLoHi {m n: Nat}: Fin (m + n) -> Fin m ⊕ Fin n
  := Fin.casesAdd Sum.inl Sum.inr

def Fin.sumHiLo {m n: Nat}: Fin (m + n) -> Fin m ⊕ Fin n
  := Fin.addCases Sum.inl Sum.inr

def Fin.sumLoHi_swap {m n: Nat} (i: Fin (m + n))
  : i.sumLoHi.swap = (i.cast (Nat.add_comm m n)).sumHiLo := by
    simp only [
      sumLoHi, casesAdd, eq_rec_constant, sumHiLo, addCases,
      coe_cast, cast_trans, cast_eq_self]
    split <;> rfl

def Fin.sumHiLo_swap {m n: Nat} (i: Fin (m + n))
  : i.sumHiLo.swap = (i.cast (Nat.add_comm m n)).sumLoHi := by
    simp only [
      sumLoHi, casesAdd, eq_rec_constant, sumHiLo, addCases,
      coe_cast, cast_trans, cast_eq_self]
    split <;> rfl

theorem Fin.addNat_cast_natAdd {n: Nat} (i: Fin n) (k: Nat)
  : i.addNat k = (i.natAdd k).cast (by rw [Nat.add_comm])
  := by simp

theorem Fin.natAdd_cast_addNat {n: Nat} (i: Fin n) (k: Nat)
  : i.natAdd k = (i.addNat k).cast (by rw [Nat.add_comm])
  := by simp

def liftnFin' {n m} (k: Nat) (ρ: Fin n -> Fin m): Fin (k + n) -> Fin (k + m)
  := Fin.addCases (Fin.castAdd m) (Fin.natAdd k ∘ ρ)

def liftnFin {n m} (k: Nat) (ρ: Fin n -> Fin m): Fin (n + k) -> Fin (m + k)
  := Fin.casesAdd (λi => (ρ i).addNat k) (λi => i.addCast m)

-- Note: this is the one without casts, so having a liftnFin_succ would be confusing...
-- This ordering is meant to coincide with Function.iterate, though...
def liftnFin_succ' {n m} (k: Nat)
  : @liftnFin n m (k.succ) = liftFin ∘ @liftnFin n m k := by
  funext ρ ⟨i, Hi⟩
  cases i with
  | zero => simp only [liftnFin, Fin.casesAdd, Nat.zero_eq, Nat.zero_lt_succ, ↓reduceDite]; rfl
  | succ i =>
    simp only [
      liftnFin, Fin.casesAdd, Fin.castLT_mk, Fin.subNat_mk, Fin.addNat_mk,
      Nat.succ_sub_succ_eq_sub, eq_rec_constant, Function.comp_apply, liftFin, Fin.cases_succ',
      Nat.succ_lt_succ_iff
    ]
    split <;> rfl

-- def liftnFin'_zero_cast {n m} (ρ: Fin n -> Fin m): liftnFin' 0 ρ = cast (by simp) ρ := by
--   funext i; apply Fin.ext; simp [liftnFin', Fin.addCases, Fin.natAdd, Fin.cast]



-- def liftnFin_succ {n m} (k: Nat): @liftnFin n m (k.succ) = cast
--     (by simp only [Nat.add_succ, Nat.succ_add])
--     (@liftnFin n.succ m.succ k ∘ liftFin)
--   := by sorry

/-
Modifying weakenings
-/

def shiftWk (ρ: Nat -> Nat): Nat -> Nat := ρ ∘ Nat.succ
def predWk (ρ: Nat -> Nat) : Nat -> Nat := Nat.pred ∘ ρ
def unliftWk (ρ: Nat -> Nat): Nat -> Nat := predWk (shiftWk ρ)
def unliftWk_liftWk_id (ρ: Nat -> Nat): unliftWk (liftWk ρ) = ρ := by
  funext n
  cases n <;> rfl
def zero_zero_liftWk_unliftWk (ρ: Nat -> Nat)
  (H: ρ 0 = 0) (H': ∀n: ℕ, ρ n.succ ≠ 0): liftWk (unliftWk ρ) = ρ := by
  funext n
  cases n with
  | zero => exact H.symm
  | succ n =>
    simp [
      liftWk, unliftWk, shiftWk, predWk,
      <-Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_ne_zero (H' n)]
def predWk_stepWk_id (ρ: Nat -> Nat): predWk (stepWk ρ) = ρ := by
  funext n
  cases n <;> rfl
def zero_zero_predWk_liftWk_shiftWk {ρ: Nat -> Nat} (H: ρ 0 = 0)
  : predWk (liftWk (shiftWk ρ)) = ρ := by
  funext n
  cases n with
  | zero => exact H.symm
  | succ _ => rfl
def unliftWk_stepWk_shiftWk (ρ: Nat -> Nat): unliftWk (stepWk ρ) = shiftWk ρ := by
  funext n
  cases n <;> rfl
def stepWk_predWk_nz_id (ρ: Nat -> Nat) (H: ∀n: ℕ, ρ n ≠ 0): stepWk (predWk ρ) = ρ := by
  funext n; exact Nat.succ_pred_eq_of_ne_zero (H n)

/-
Weakening on natural numbers
-/

inductive WkNat: (ℕ -> ℕ) -> ℕ -> ℕ -> Prop
  | nil ρ: WkNat ρ 0 0
  | lift: WkNat ρ m n -> WkNat (liftWk ρ) (m.succ) (n.succ)
  | step: WkNat ρ m n -> WkNat (stepWk ρ) (m.succ) n

def WkNat.comp {ρ σ: ℕ -> ℕ} {n m k: ℕ}
  : WkNat ρ m n -> WkNat σ n k -> WkNat (ρ ∘ σ) m k
  | nil _, nil _ => nil _
  | lift R, lift R' => liftWk_comp _ _ ▸ lift (comp R R')
  | lift R, step R' => step (comp R R')
  | step R, R' => step (comp R R')

def WkNat.bounded {ρ m n k}: WkNat ρ m n -> (k < n) -> (ρ k < m)
  | lift R, H => match k with
    | 0 => by simp [liftWk]
    | k + 1 => Nat.succ_lt_succ (R.bounded (Nat.lt_of_succ_lt_succ H))
  | step R, H => Nat.succ_lt_succ (R.bounded H)

def WkNat.noalias {ρ m n k}: WkNat ρ m n -> (k ≥ n) -> (ρ k ≥ m)
  | nil _, H => Nat.zero_le _
  | lift R, H => match k with
    | 0 => by cases H
    | k + 1 => Nat.succ_le_succ (R.noalias (Nat.le_of_succ_le_succ H))
  | step R, H => Nat.succ_le_succ (R.noalias H)

def WkNat.inj {ρ m n k k'}: WkNat ρ m n -> (k < n) -> (k' < n) -> (ρ k = ρ k') -> k = k'
  | lift R, H, H', Heq => match k, k' with
    | 0, 0 => rfl
    | 0, k + 1 => by cases Heq
    | k + 1, 0 => by cases Heq
    | k + 1, k' + 1 => congrArg
      Nat.succ
      (R.inj (Nat.lt_of_succ_lt_succ H)
        (Nat.lt_of_succ_lt_succ H')
        (Nat.succ_injective Heq))
  | step R, H, H', Heq => Nat.succ_injective (congrArg
    Nat.succ
    (R.inj H H' (Nat.succ_injective Heq)))

def WkNat.mono {ρ m n k k'}: WkNat ρ m n -> (k < n) -> (k' < n) -> (k ≤ k') -> (ρ k ≤ ρ k')
  | lift R, Hk, Hk', H => match k, k' with
    | 0, _ => Nat.zero_le _
    | n + 1, 0 => by cases H
    | n + 1, m + 1 => Nat.succ_le_succ (mono R
      (Nat.lt_of_succ_lt_succ Hk)
      (Nat.lt_of_succ_lt_succ Hk')
      (Nat.le_of_succ_le_succ H))
  | step R, Hk, Hk', H => Nat.succ_le_succ (mono R Hk Hk' H)

def WkNat.nz {ρ m n} (k: ℕ): WkNat ρ (m + 1) n -> ρ 0 ≠ 0 -> ρ k ≠ 0
  | step _, H => by simp [stepWk]

def WkNat.bound_le {ρ m n}: WkNat ρ m n -> n ≤ m
  | nil _ => le_refl _
  | lift R => Nat.succ_le_succ (R.bound_le)
  | step R => Nat.le_step (R.bound_le)

--TODO: WkNat <==> bounded ∧ noalias ∧ inj ?

def WkNat.app {ρ m n} (R: WkNat ρ m n) (k: Fin n): Fin m
  := ⟨ρ k.val, R.bounded k.isLt⟩

theorem WkNat.app_val {ρ m n} (R: WkNat ρ m n) (k: Fin n): (R.app k).val = ρ k.val
  := rfl

def WkNat.app_injective {ρ m n} (R: WkNat ρ m n): Function.Injective R.app
  := λk k' H => Fin.eq_of_val_eq (WkNat.inj R k.isLt k'.isLt (Fin.val_eq_of_eq H))

inductive WkNatT: (ℕ -> ℕ) -> ℕ -> ℕ -> Type
  | nil ρ: WkNatT ρ 0 0
  | lift: WkNatT ρ m n -> WkNatT (liftWk ρ) (m.succ) (n.succ)
  | step: WkNatT ρ m n -> WkNatT (stepWk ρ) (m.succ) n

theorem WkNatT.nil_eq: (R: WkNatT ρ 0 0) -> R = nil ρ
  | nil _ => rfl

def WkNatT.comp {ρ σ: ℕ -> ℕ} {n m k: ℕ}
  : WkNatT ρ n m -> WkNatT σ m k -> WkNatT (ρ ∘ σ) n k
  | nil _, nil _ => nil _
  | lift R, lift R' => liftWk_comp _ _ ▸ lift (comp R R')
  | lift R, step R' => step (comp R R')
  | step R, R' => step (comp R R')

def WkNat.toWkNatT {ρ n m} (R: WkNat ρ n m): WkNatT ρ n m
  := match m, n with
  | 0, 0 => WkNatT.nil ρ
  | n + 1, 0 => False.elim (by cases R)
  | n, m + 1 => if p: ρ 0 = 0
    then
      match n with
      | 0 => False.elim (by cases R; cases p)
      | n + 1 =>
        have H := zero_zero_liftWk_unliftWk _ p
          (λn => by cases R <;> simp [liftWk, stepWk])
        let R': WkNat (unliftWk ρ) m n := by
          cases R with
          | lift R => exact unliftWk_liftWk_id _ ▸ R
          | step R => cases p
        H ▸ (WkNatT.lift (WkNat.toWkNatT R'))
    else
      let R': WkNat (predWk ρ) m n := by
        cases R with
        | lift R => exfalso; exact p rfl
        | step R => exact predWk_stepWk_id _ ▸ R
      (stepWk_predWk_nz_id ρ (λn => R.nz n p)) ▸ (WkNatT.step (WkNat.toWkNatT R'))

theorem WkNatT.toWkNat {ρ n m}: WkNatT ρ n m -> WkNat ρ n m
  | WkNatT.nil _ => WkNat.nil _
  | WkNatT.lift R => WkNat.lift (WkNatT.toWkNat R)
  | WkNatT.step R => WkNat.step (WkNatT.toWkNat R)

theorem WkNatT.eq_toWkNat_toWkNatT {ρ n m}:
  (R: WkNatT ρ n m) -> R.toWkNat.toWkNatT = R
  | nil _ => rfl
  | lift R => by simp [WkNat.toWkNatT, liftWk, eq_toWkNat_toWkNatT R]
  | step R => by simp [WkNat.toWkNatT, stepWk, eq_toWkNat_toWkNatT R]

theorem WkNatT.uniq {ρ n k} (R R': WkNatT ρ n k): R = R' := by
  rw [<-eq_toWkNat_toWkNatT R, <-eq_toWkNat_toWkNatT R']

instance {ρ n k}: Subsingleton (WkNatT ρ n k) where
  allEq := WkNatT.uniq

def WkNatT.app {ρ m n} (R: WkNatT ρ m n) (k: Fin n): Fin m
  := ⟨ρ k.val, R.toWkNat.bounded k.isLt⟩

def Fin.lift {n m} (ρ: Fin n -> Fin m): Fin (n + 1) -> Fin (m + 1)
  := Fin.cases 0 (Fin.succ ∘ ρ)

theorem Fin.lift_id {n}: Fin.lift (@id (Fin n)) = id := by
  funext ⟨k, H⟩
  cases k with
  | zero => rfl
  | succ k => simp [Fin.lift, Fin.succ]

-- TODO: liftn, etc

def WkNatT.app_rec {ρ m n}: WkNatT ρ m n -> Fin n -> Fin m
  | nil _ => id
  | lift R => Fin.lift (R.app_rec)
  | step R => Fin.succ ∘ R.app_rec

theorem WkNatT.app_rec_eq_app {ρ n m}: (R: WkNatT ρ n m) -> R.app_rec = R.app
  | nil _ => by funext ⟨_, H⟩; cases H
  | lift R => by
    funext ⟨k, Hk⟩;
    cases k with
    | zero => rfl
    | succ k =>
      simp [app_rec, app, liftWk, Fin.succ, Fin.lift, app_rec_eq_app R]
  | step R => by funext k; simp only [app_rec, app_rec_eq_app R]; rfl

def WkNatT.app_cases {ρ m n}: WkNatT ρ m n -> Fin n -> Fin m
  | nil _, k => k
  | lift _, 0 => 0
  | lift R, ⟨k + 1, Hk⟩ => (R.app_rec ⟨k, Nat.lt_of_succ_lt_succ Hk⟩).succ
  | step R, k => (R.app k).succ

def WkNatT.app2 {ρ m n}: WkNatT ρ m n -> Fin2 n -> Fin2 m
  | nil _, k => k
  | lift _, Fin2.fz => Fin2.fz
  | lift R, Fin2.fs f => Fin2.fs (R.app2 f)
  | step R, k => Fin2.fs (R.app2 k)

inductive NatWk: ℕ -> ℕ -> Type
  | nil: NatWk 0 0
  | lift: NatWk m n -> NatWk (m.succ) (n.succ)
  | step: NatWk m n -> NatWk (m.succ) n

def NatWk.app {m n}: NatWk m n -> Fin n -> Fin m
  | nil => id
  | lift R => Fin.lift (R.app)
  | step R => Fin.succ ∘ R.app

def NatWk.toFn {m n}: NatWk m n -> Nat -> Nat
  | nil => id
  | lift R => liftWk R.toFn
  | step R => stepWk R.toFn

def NatWk.toWkNat {m n}: (ρ: NatWk m n) -> WkNatT ρ.toFn m n
  | nil => WkNatT.nil _
  | lift R => WkNatT.lift (toWkNat R)
  | step R => WkNatT.step (toWkNat R)

def WkNatT.toNatWk {ρ m n}: WkNatT ρ m n -> NatWk m n
  | WkNatT.nil _ => NatWk.nil
  | WkNatT.lift R => NatWk.lift (toNatWk R)
  | WkNatT.step R => NatWk.step (toNatWk R)

-- theorem: equal on fin, etc

theorem NatWk.is_wk {m n} (ρ: NatWk m n): WkNat ρ.toFn m n := ρ.toWkNat.toWkNat

structure WkFin (ρ: ℕ -> ℕ) (n: ℕ) (m: ℕ): Prop where
  bounded: ∀i: ℕ, i < n -> ρ i < m
  mono: ∀i: ℕ, i < n -> ∀j: ℕ, j < i -> ρ j < ρ i

theorem WkFin.id_ext {n m: ℕ} (Hnm: n ≤ m): WkFin id n m where
  bounded := λ_ H => Nat.lt_of_lt_of_le H Hnm
  mono := λ_ _ _ H => H

theorem WkFin.id (n: ℕ): WkFin id n n where
  bounded := λ_ H => H
  mono := λ_ _ _ H => H

--TODO: lift

--TODO: liftn

--TODO: step

--TODO: comp

--TODO: WkNat <==> WkFin?

--TODO: app on Fin

--TODO: app on Fin2

-- theorem WkFin.le {ρ n m}: WkFin ρ n m -> n ≤ m := sorry

--TODO: tuple weakening, based on WkFin as WkList is based on WkNat...

--TODO: factor into files...

inductive WkList {A}: (Nat -> Nat) -> List A -> List A -> Prop
  | nil ρ: WkList ρ [] []
  | lift {ρ xs ys} x: WkList ρ xs ys -> WkList (liftWk ρ) (x::xs) (x::ys)
  | step {ρ xs ys} x: WkList ρ xs ys -> WkList (stepWk ρ) (x::xs) ys

def WkList.id {A}: (Γ: List A) -> WkList id Γ Γ
  | [] => nil _
  | x::Γ => liftWk_id ▸ lift x (id Γ)

def WkList.wk1 {A} (x: A) (Γ: List A): WkList (stepWk _root_.id) (x::Γ) Γ
  := (id Γ).step x

def WkList.toWkNat {A} {ρ: Nat -> Nat} {xs ys: List A}
  : WkList ρ xs ys -> WkNat ρ xs.length ys.length
  | nil _ => WkNat.nil _
  | lift _ R => WkNat.lift (toWkNat R)
  | step _ R => WkNat.step (toWkNat R)

theorem WkList.get_eq {A} {ρ} {Γ Δ: List A}
  : (R: WkList ρ Γ Δ) -> ∀k: Fin Δ.length, Γ.get (R.toWkNat.app k) = Δ.get k
  | lift _ R, ⟨0, _⟩ => rfl
  | lift _ R, ⟨n + 1, Hn⟩ => R.get_eq ⟨_, Nat.lt_of_succ_lt_succ Hn⟩
  | step _ R, _ => R.get_eq _

theorem WkList.lift_head_eq {A} {ρ} {Γ Δ: List A}
  (x y) (R: WkList (liftWk ρ) (x::Γ) (y::Δ))
  : x = y
  := R.get_eq ⟨0, by simp⟩

theorem WkList.lift_rest {A} {ρ} {Γ Δ: List A}
  {x y}: WkList (liftWk ρ) (x::Γ) (y::Δ) -> WkList ρ Γ Δ
  := by
    generalize H: liftWk ρ = ρ'
    intro R
    cases R with
    | lift R => rw [liftWk_injective H]; assumption
    | step R => exact (liftWk_ne_stepWk _ _ H).elim

theorem WkList.step_rest {A} {ρ} {Γ Δ: List A}
  {x}: WkList (stepWk ρ) (x::Γ) (Δ) -> WkList ρ Γ Δ
  := by
    generalize H: stepWk ρ = ρ'
    intro R
    cases R with
    | lift R => exact (liftWk_ne_stepWk _ _ H.symm).elim
    | step R => rw [stepWk_injective H]; assumption

theorem WkList.getElem_eq {A} {ρ} {Γ Δ: List A} (R: WkList ρ Γ Δ)
  : ∀k: Fin Δ.length, Γ[R.toWkNat.app k] = Δ[k]
  := R.get_eq

theorem WkList.get?_eq {A} {ρ} {Γ Δ: List A}
  : (R: WkList ρ Γ Δ) -> ∀k: ℕ, Γ.get? (ρ k) = Δ.get? k
  | nil _, _ => rfl
  | lift _ R, 0 => rfl
  | lift _ R, n + 1 => R.get?_eq _
  | step _ R, _ => R.get?_eq _

theorem WkList.getElem?_eq {A} {ρ} {Γ Δ: List A} (R: WkList ρ Γ Δ)
  : ∀k: ℕ, Γ[ρ k]? = Δ[k]?
  | _ => by simp [R.get?_eq]

inductive WkListT {A}: (Nat -> Nat) -> List A -> List A -> Type
  | nil ρ: WkListT ρ [] []
  | lift {ρ xs ys} x: WkListT ρ xs ys -> WkListT (liftWk ρ) (x::xs) (x::ys)
  | step {ρ xs ys} x: WkListT ρ xs ys -> WkListT (stepWk ρ) (x::xs) ys

def WkList.toWkNatT {A} {ρ: Nat -> Nat} {xs ys: List A} (R: WkList ρ xs ys)
  : WkNatT ρ xs.length ys.length := R.toWkNat.toWkNatT

def WkList.toWkListT_helper {A} {ρ: Nat -> Nat}
  : {xs ys: List A} -> WkList ρ xs ys
    -> WkNatT ρ xs.length ys.length -> WkListT ρ xs ys
  | [], [], _, WkNatT.nil _ => WkListT.nil _
  | _::_, _::_, R, WkNatT.lift Rn =>
    R.lift_head_eq ▸ WkListT.lift _ (toWkListT_helper R.lift_rest Rn)
  | _::_, _, R, WkNatT.step Rn => WkListT.step _ (toWkListT_helper R.step_rest Rn)

def WkList.toWkListT {A} {ρ: Nat -> Nat} {xs ys: List A} (R: WkList ρ xs ys)
  : WkListT ρ xs ys
  := R.toWkListT_helper R.toWkNatT

def WkList.toWkListT_eq {A} {ρ} {Γ Δ: List A}
  : (R: WkList ρ Γ Δ) -> (R': WkListT ρ Γ Δ) -> R.toWkListT = R'
  | _, WkListT.nil _ => rfl
  | R, WkListT.lift _ R' => by
    rw [toWkListT, toWkNatT]
    rw [<-toWkListT_eq R.lift_rest R']
    simp only [WkNat.toWkNatT, liftWk, Nat.add_eq, Nat.add_zero, dite_true]
    rfl
  | R, WkListT.step _ R' => by
    rw [toWkListT, toWkNatT]
    rw [<-toWkListT_eq R.step_rest R']
    simp only [
      stepWk, List.length_cons, WkNat.toWkNatT, Function.comp_apply,
      Nat.succ_ne_zero, dite_false, toWkListT_helper]
    rfl

theorem WkListT.toWkList {A} {ρ: Nat -> Nat} {xs ys: List A}
  : WkListT ρ xs ys -> WkList ρ xs ys
  | nil _ => WkList.nil _
  | lift _ R => WkList.lift _ (toWkList R)
  | step _ R => WkList.step _ (toWkList R)

theorem WkListT.uniq {A} {ρ: Nat -> Nat} {xs ys: List A}
  (R R': WkListT ρ xs ys): R = R'
  := (R.toWkList.toWkListT_eq R).symm.trans (R.toWkList.toWkListT_eq R')

instance: Subsingleton (WkListT Γ n A) where
  allEq := WkListT.uniq

inductive ListWk {A}: List A -> List A -> Type
  | nil: ListWk [] []
  | lift x: ListWk xs ys -> ListWk (x::xs) (x::ys)
  | step x: ListWk xs ys -> ListWk (x::xs) ys

def ListWk.toNatWk {A} {Γ Δ: List A}: ListWk Γ Δ -> NatWk Γ.length Δ.length
  | ListWk.nil => NatWk.nil
  | ListWk.lift _ R => NatWk.lift (ListWk.toNatWk R)
  | ListWk.step _ R => NatWk.step (ListWk.toNatWk R)

inductive OrdWk {A} [PartialOrder A]: List A -> List A -> Type
  | nil: OrdWk [] []
  | lift: x ≥ y -> OrdWk xs ys -> OrdWk (x::xs) (y::ys)
  | step: OrdWk xs ys -> OrdWk (x::xs) ys

def OrdWk.toNatWk {A} [PartialOrder A] {Γ Δ: List A}: OrdWk Γ Δ -> NatWk Γ.length Δ.length
  | OrdWk.nil => NatWk.nil
  | OrdWk.lift H R => NatWk.lift (OrdWk.toNatWk R)
  | OrdWk.step R => NatWk.step (OrdWk.toNatWk R)

def ListWk.toOrdWk {A} [PartialOrder A] {Γ Δ: List A}: ListWk Γ Δ -> OrdWk Γ Δ
  | ListWk.nil => OrdWk.nil
  | ListWk.lift _ R => OrdWk.lift (le_refl _) (ListWk.toOrdWk R)
  | ListWk.step _ R => OrdWk.step (ListWk.toOrdWk R)

theorem ListWk.toOrdWk_NatWk {A} [PartialOrder A] {Γ Δ: List A} (R: ListWk Γ Δ)
  : ListWk.toNatWk R = OrdWk.toNatWk (ListWk.toOrdWk R) := by
  induction R <;> simp [ListWk.toOrdWk, OrdWk.toNatWk, ListWk.toNatWk, *]

inductive At {A}: List A -> ℕ -> A -> Prop
  | head (x xs): At (x::xs) 0 x
  | tail (x) {xs n y}: At xs n y -> At (x::xs) (n + 1) y

theorem At.head_eq: At (y::Γ) 0 x -> x = y
  | At.head _ _ => rfl

theorem At.to_tail: At (x::Γ) (n + 1) y -> At Γ n y
  | At.tail _ R => R

theorem At.wk {ρ Γ Δ}: WkList ρ Γ Δ -> At Δ n x -> At Γ (ρ n) x
  | WkList.lift _ R, At.head _ _ => At.head _ _
  | WkList.lift _ R, At.tail _ R'
  | WkList.step _ R, R' => At.tail _ (wk R R')

inductive AtT {A}: List A -> ℕ -> A -> Type
  | head (x xs): AtT (x::xs) 0 x
  | tail (x) {xs n y}: AtT xs n y -> AtT (x::xs) (n + 1) y

theorem AtT.toAt: AtT Γ n A -> At Γ n A
  | AtT.head x xs => At.head x xs
  | AtT.tail x R => At.tail x R.toAt

def AtT.to_tail: AtT (x::Γ) (n + 1) x -> AtT Γ n x
  | AtT.tail _ R => R

instance: Subsingleton (AtT Γ n A) where
  allEq := by
    intro R R'
    induction R with
    | head x xs => cases R'; rfl
    | tail x R I => cases R'; rw [I]

def At.toAtT {α}: {Γ: List α} -> {n: ℕ} -> {x: α} -> At Γ n x -> AtT Γ n x
  | [], _, _, R => False.elim (by cases R)
  | x::Γ, 0, y, R =>
    have H: x = y := by cases R; rfl
    H ▸ AtT.head x Γ
  | x::Γ, n + 1, _, R => AtT.tail x (At.toAtT (by cases R; assumption))

def AtT.wk {ρ Γ Δ} (R: WkList ρ Γ Δ) (i: AtT Δ n x): AtT Γ (ρ n) x
  := (i.toAt.wk R).toAtT

def AtT.wk_t {ρ Γ Δ}: WkListT ρ Γ Δ -> AtT Δ n x -> AtT Γ (ρ n) x
  | WkListT.lift _ R, AtT.head _ _ => AtT.head _ _
  | WkListT.lift _ R, AtT.tail _ R'
  | WkListT.step _ R, R' => AtT.tail _ (wk_t R R')

inductive Ix {A}: List A -> A -> Type
  | head (x xs): Ix (x::xs) x
  | tail (x) {xs y}: Ix xs y -> Ix (x::xs) y

def Ix.toNat: Ix Γ x -> ℕ
  | head _x _ => 0
  | tail _ R => R.toNat + 1

def Ix.toAtT: (i: Ix Γ x) -> AtT Γ i.toNat x
  | head _x _ => AtT.head _ _
  | tail _ i => AtT.tail _ i.toAtT

theorem Ix.toAt (i: Ix Γ x): At Γ i.toNat x
  := i.toAtT.toAt

def Ix.wk: ListWk Γ Δ -> Ix Δ A -> Ix Γ A
| ListWk.lift _A ρ, Ix.head _ _ => Ix.head _ _
| ListWk.lift _A ρ, Ix.tail _ v
| ListWk.step _ ρ, v => Ix.tail _ (wk ρ v)

def AtT.toIx: AtT Γ n x -> Ix Γ x
  | AtT.head _x _ => Ix.head _ _
  | AtT.tail _ i => Ix.tail _ i.toIx

def At.toIx: At Γ n x -> Ix Γ x
  := AtT.toIx ∘ At.toAtT

--TODO: Ord Ix, At, etc...
