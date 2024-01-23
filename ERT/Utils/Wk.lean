import Mathlib.Order.Monotone.Basic
import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Fin2

/-!
# Weakenings

Definitions and utilities for weakening de-Bruijn indices
-/

def stepWk (ρ: Nat -> Nat): Nat -> Nat := Nat.succ ∘ ρ

def liftWk (ρ: Nat -> Nat): Nat -> Nat
  | 0 => 0
  | n + 1 => (ρ n) + 1

def liftWk_id: liftWk id = id := by funext n; cases n <;> simp [liftWk]

def liftWk_comp (ρ σ: Nat -> Nat): liftWk (ρ ∘ σ) = liftWk ρ ∘ liftWk σ := by
 funext n; cases n <;> simp [liftWk]

def liftWk_comp_succ (ρ: Nat -> Nat): liftWk ρ ∘ Nat.succ = Nat.succ ∘ ρ := by
  funext n; cases n <;> rfl

def liftWk_ne_stepWk (ρ σ: Nat -> Nat): liftWk ρ ≠ stepWk σ :=
  have H: (liftWk ρ 0) ≠ (stepWk σ 0) := by simp [liftWk, stepWk]
  λH' => H (by rw [H'])

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
  | lift: WkNat ρ n m -> WkNat (liftWk ρ) (n.succ) (m.succ)
  | step: WkNat ρ n m -> WkNat (stepWk ρ) n (m.succ)

def WkNat.comp {ρ σ: ℕ -> ℕ} {n m k: ℕ}
  : WkNat ρ n m -> WkNat σ m k -> WkNat (σ ∘ ρ) n k
  | nil _, nil _ => nil _
  | lift R, lift R' => liftWk_comp _ _ ▸ lift (comp R R')
  | step R, lift R' => step (comp R R')
  | R, step R' => step (comp R R')

def WkNat.bounded {ρ n m k}: WkNat ρ n m -> (k < n) -> (ρ k < m)
  | lift R, H => match k with
    | 0 => by simp [liftWk]
    | k + 1 => Nat.succ_lt_succ (R.bounded (Nat.lt_of_succ_lt_succ H))
  | step R, H => Nat.succ_lt_succ (R.bounded H)

def WkNat.noalias {ρ n m k}: WkNat ρ n m -> (k ≥ n) -> (ρ k ≥ m)
  | nil _, H => Nat.zero_le _
  | lift R, H => match k with
    | 0 => by cases H
    | k + 1 => Nat.succ_le_succ (R.noalias (Nat.le_of_succ_le_succ H))
  | step R, H => Nat.succ_le_succ (R.noalias H)

def WkNat.inj {ρ n m k k'}: WkNat ρ n m -> (k < n) -> (k' < n) -> (ρ k = ρ k') -> k = k'
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

def WkNat.mono {ρ n m k k'}: WkNat ρ n m -> (k < n) -> (k' < n) -> (k ≤ k') -> (ρ k ≤ ρ k')
  | lift R, Hk, Hk', H => match k, k' with
    | 0, _ => Nat.zero_le _
    | n + 1, 0 => by cases H
    | n + 1, m + 1 => Nat.succ_le_succ (mono R
      (Nat.lt_of_succ_lt_succ Hk)
      (Nat.lt_of_succ_lt_succ Hk')
      (Nat.le_of_succ_le_succ H))
  | step R, Hk, Hk', H => Nat.succ_le_succ (mono R Hk Hk' H)

def WkNat.nz {ρ n m} (k: ℕ): WkNat ρ n (m + 1) -> ρ 0 ≠ 0 -> ρ k ≠ 0
  | step _, H => by simp [stepWk]

def WkNat.bound_le {ρ n m}: WkNat ρ n m -> n ≤ m
  | nil _ => le_refl _
  | lift R => Nat.succ_le_succ (R.bound_le)
  | step R => Nat.le_step (R.bound_le)

--TODO: WkNat <==> bounded ∧ noalias ∧ inj ?

def WkNat.app {ρ n m} (R: WkNat ρ n m) (k: Fin n): Fin m
  := ⟨ρ k.val, R.bounded k.isLt⟩

theorem WkNat.app_val {ρ n m} (R: WkNat ρ n m) (k: Fin n): (R.app k).val = ρ k.val
  := rfl

def WkNat.app_injective {ρ n m} (R: WkNat ρ n m): Function.Injective R.app
  := λk k' H => Fin.eq_of_val_eq (WkNat.inj R k.isLt k'.isLt (Fin.val_eq_of_eq H))

inductive WkNatT: (ℕ -> ℕ) -> ℕ -> ℕ -> Type
  | nil ρ: WkNatT ρ 0 0
  | lift: WkNatT ρ n m -> WkNatT (liftWk ρ) (n.succ) (m.succ)
  | step: WkNatT ρ n m -> WkNatT (stepWk ρ) n (m.succ)

theorem WkNatT.nil_eq: (R: WkNatT ρ 0 0) -> R = nil ρ
  | nil _ => rfl

def WkNatT.comp {ρ σ: ℕ -> ℕ} {n m k: ℕ}
  : WkNatT ρ n m -> WkNatT σ m k -> WkNatT (σ ∘ ρ) n k
  | nil _, nil _ => nil _
  | lift R, lift R' => liftWk_comp _ _ ▸ lift (comp R R')
  | step R, lift R' => step (comp R R')
  | R, step R' => step (comp R R')

def WkNat.toWkNatT {ρ n m} (R: WkNat ρ n m): WkNatT ρ n m
  := match n, m with
  | 0, 0 => WkNatT.nil ρ
  | n + 1, 0 => False.elim (by cases R)
  | n, m + 1 => if p: ρ 0 = 0
    then
      match n with
      | 0 => False.elim (by cases R; cases p)
      | n + 1 =>
        have H := zero_zero_liftWk_unliftWk _ p
          (λn => by cases R <;> simp [liftWk, stepWk])
        let R': WkNat (unliftWk ρ) n m := by
          cases R with
          | lift R => exact unliftWk_liftWk_id _ ▸ R
          | step R => cases p
        H ▸ (WkNatT.lift (WkNat.toWkNatT R'))
    else
      let R': WkNat (predWk ρ) n m := by
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

instance WkNatT.instSubsingleton {ρ n k}: Subsingleton (WkNatT ρ n k) where
  allEq := WkNatT.uniq

def WkNatT.app {ρ n m} (R: WkNatT ρ n m) (k: Fin n): Fin m
  := ⟨ρ k.val, R.toWkNat.bounded k.isLt⟩

def WkNatT.app_rec {ρ n m}: WkNatT ρ n m -> Fin n -> Fin m
  | nil _, k => k
  | lift _, 0 => 0
  | lift R, ⟨k + 1, Hk⟩ => (R.app_rec ⟨k, Nat.lt_of_succ_lt_succ Hk⟩).succ
  | step R, k => (R.app_rec k).succ

theorem WkNatT.app_rec_eq_app {ρ n m}: (R: WkNatT ρ n m) -> R.app_rec = R.app
  | nil _ => by funext ⟨_, H⟩; cases H
  | lift R => by
    funext ⟨k, Hk⟩;
    cases k with
    | zero => rfl
    | succ k =>
      simp [app_rec, app, liftWk, Fin.succ, app_rec_eq_app R]
  | step R => by funext k; simp only [app_rec, app_rec_eq_app R]; rfl

def WkNatT.app_cases {ρ n m}: WkNatT ρ n m -> Fin n -> Fin m
  | nil _, k => k
  | lift _, 0 => 0
  | lift R, ⟨k + 1, Hk⟩ => (R.app_rec ⟨k, Nat.lt_of_succ_lt_succ Hk⟩).succ
  | step R, k => (R.app k).succ

def WkNatT.app2 {ρ n m}: WkNatT ρ n m -> Fin2 n -> Fin2 m
  | nil _, k => k
  | lift _, Fin2.fz => Fin2.fz
  | lift R, Fin2.fs f => Fin2.fs (R.app2 f)
  | step R, k => Fin2.fs (R.app2 k)
