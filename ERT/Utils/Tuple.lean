import Mathlib.Data.Fin.Tuple.Basic

def Fin.foldl_zero {α} (f: α -> Fin 0 -> α) (b: α): foldl 0 f b = b
  := rfl

theorem Fin.foldl.loop_end {α} (n: ℕ) (f: α -> Fin n -> α) (b: α): foldl.loop n f b n = b
  := by unfold loop; simp
theorem Fin.foldl.loop_zero {α} (f: α -> Fin 0 -> α) (b: α) (n: ℕ): foldl.loop 0 f b n = b
  := by unfold loop; simp
theorem Fin.foldl.loop_succ {α} (n: ℕ) (f: α -> Fin (n + 1) -> α) (b: α) (i: ℕ) (H: i < n + 1)
  : foldl.loop (n + 1) f b i = foldl.loop n (λa i => f a i.succ) (f b i) i := if H': i < n
  then by
    unfold loop
    simp only [H, ↓reduceDite, H']
    rw [loop_succ n f _ (i + 1) (Nat.succ_lt_succ H')]
    congr
    rw [Nat.mod_eq_of_lt H]
    simp only [succ_mk, Nat.cast, NatCast.natCast, ofNat'']
    apply Fin.ext
    simp only [Nat.mod_succ_eq_iff_lt]
    exact Nat.succ_lt_succ H'
  else by
    have H' := le_antisymm (Nat.le_of_not_lt H') (Nat.le_of_succ_le_succ H);
    cases H'
    unfold loop
    unfold loop
    simp
    rfl
  termination_by n - i

theorem Fin.foldl_succ_inner {α} (n: ℕ) (f: α -> Fin (n + 1) -> α) (b: α)
  : foldl (n + 1) f b = foldl n (λa i => f a i.succ) (f b 0) := by
  rw [foldl, foldl.loop_succ _ _ _ _ (by simp)]
  congr

def Fin.foldl_inner {α} (n: ℕ) (f: α -> Fin n -> α) (b: α) :=
  match n with
  | 0 => b
  | n + 1 => foldl_inner n (λa i => f a i.succ) (f b 0)

theorem Fin.foldl_eq_inner: @Fin.foldl α = Fin.foldl_inner := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => funext f b; rw [foldl_succ_inner, foldl_inner, I]

theorem Fin.foldl_succ_outer {α} (n: ℕ) (f: α -> Fin (n + 1) -> α) (b: α)
  : foldl (n + 1) f b = f (foldl n (λa i => f a i) b) (Fin.last n)
  := by induction n generalizing b with
  | zero => rfl
  | succ n I =>
    rw [foldl_succ_inner, I, foldl_succ_inner]
    congr
    funext a i
    congr
    apply Fin.ext
    rw [coe_eq_castSucc, coe_eq_castSucc, succ_castSucc]

def Fin.foldl_outer {α} (n: ℕ) (f: α -> Fin n -> α) (b: α) :=
  match n with
  | 0 => b
  | n + 1 => f (foldl_outer n (λa i => f a i) b) (Fin.last n)

theorem Fin.foldl_eq_outer: @Fin.foldl α = Fin.foldl_outer := by
  funext n
  induction n with
  | zero => rfl
  | succ n I => funext f b; rw [foldl_succ_outer, foldl_outer, I]

theorem sub_eq_succ_add_helper {a b c: ℕ} (H: a - b = c.succ): a = c.succ + b
  := Nat.eq_add_of_sub_eq (Nat.le_of_lt (Nat.lt_of_sub_eq_succ H)) H

theorem succ_sub_eq_succ_add_helper {a b c: ℕ} (H: a.succ - b = c.succ): a = c + b := by
  have H := sub_eq_succ_add_helper H
  rw [Nat.succ_add] at H
  cases H
  rfl

def Tuple.foldl {α β} {n: ℕ} (f: α -> β -> α) (a: α) (t: Fin n -> β): α :=
  Fin.foldl n (λa i => f a (t i)) a

theorem Tuple.foldl_zero {α} (f: α -> β -> α)  (t: Fin 0 -> β) (a: α): foldl f a t = a
  := rfl
theorem Tuple.foldl_init {α} (f: α -> β -> α) (t: Fin (n + 1) -> β) (a: α)
  : foldl f a t = f (foldl f a (Fin.init t)) (t n) := by
  unfold foldl
  rw [Fin.foldl_succ_outer]
  congr
  funext a i
  simp [Fin.castSucc]
  congr
  apply Fin.ext
  simp
theorem Tuple.foldl_tail {α} (f: α -> β -> α) (t: Fin (n + 1) -> β) (b: α)
  : foldl f b t = foldl f (f b (t 0)) (Fin.tail t) := by
  unfold foldl
  rw [Fin.foldl_succ_inner]
  rfl

theorem Tuple.nat_max_le_base (a: ℕ) (t: Fin n -> ℕ): a ≤ foldl Nat.max a t := by
  induction n generalizing a with
  | zero => rfl
  | succ n I =>
    simp [foldl_tail]
    exact le_trans (le_max_left _ _) (I _ _)

theorem Tuple.nat_max_le_ith (a: ℕ) (t: Fin n -> ℕ) (i: Fin n)
  : t i ≤ foldl Nat.max a t := by
  induction n generalizing a with
  | zero => exact i.elim0
  | succ n I =>
    rw [foldl_tail]
    match i with
    | ⟨0, Hi⟩ => exact le_trans (Nat.le_max_right _ _) (nat_max_le_base _ _)
    | ⟨i + 1, Hi⟩ => exact (I _ (Fin.tail t) ⟨i, Nat.lt_of_succ_lt_succ Hi⟩)

theorem Tuple.nat_max_le_base_and_ith (a: ℕ) (t: Fin n -> ℕ)
  : a ≤ foldl Nat.max a t ∧ ∀i, t i ≤ foldl Nat.max a t :=
  ⟨nat_max_le_base _ _, nat_max_le_ith _ _⟩

theorem Tuple.nat_max_le_of_base_le_of_ith_le (a: ℕ) (t: Fin n -> ℕ) (b: ℕ)
  (Hab: a ≤ b) (Hith: ∀i, t i ≤ b): foldl Nat.max a t ≤ b := by
  induction n generalizing a with
  | zero => exact Hab
  | succ n I =>
    rw [foldl_tail]
    exact I _ _ (Nat.max_le_of_le_of_le Hab (Hith 0)) (λi => Hith i.succ)

def Fin.addCast {m: Nat} (i: Fin m) (n: Nat): Fin (n + m)
  := i.castLE (by simp)

def Fin.casesAdd {m n: Nat} {motive: Fin (m + n) -> Sort u}
  (left: ∀ i: Fin m, motive (addNat i n))
  (right: ∀ i: Fin n, motive (addCast i m))
  (i: Fin (m + n)): motive i
  := if hi : (i : Nat) < n then right (i.castLT hi)
  else Fin.addNat_subNat (Nat.le_of_not_lt hi) ▸ left (subNat n i (Nat.le_of_not_lt hi))

def Fin.prepend {m n: Nat} (a: Fin m -> α) (b: Fin n -> α): Fin (m + n) -> α
  := Fin.casesAdd a b

def Fin.sumHiLo {m n: Nat}: Fin (m + n) -> Fin m ⊕ Fin n
  := Fin.addCases Sum.inl Sum.inr

theorem Fin.append_eq_sumHiLo_elim {m n: Nat} (a: Fin m -> α) (b: Fin n -> α) (i: Fin (m + n))
  : (Fin.append a b) i = i.sumHiLo.elim a b
  := by simp only [append, addCases, eq_rec_constant, sumHiLo]; split <;> rfl

def Fin.sumLoHi {m n: Nat}: Fin (m + n) -> Fin m ⊕ Fin n
  := Fin.casesAdd Sum.inl Sum.inr

theorem Fin.prepend_eq_sumLoHi_elim {m n: Nat} (a: Fin m -> α) (b: Fin n -> α) (i: Fin (m + n))
  : (Fin.prepend a b) i = i.sumLoHi.elim a b
  := by simp only [prepend, casesAdd, eq_rec_constant, sumLoHi]; split <;> rfl

theorem Fin.sumLoHi_swap {m n: Nat} (i: Fin (m + n))
  : i.sumLoHi.swap = (i.cast (Nat.add_comm m n)).sumHiLo := by
    simp only [
      sumLoHi, casesAdd, eq_rec_constant, sumHiLo, addCases,
      coe_cast, cast_trans, cast_eq_self]
    split <;> rfl

theorem Fin.swap_comp_sumLoHi (m n: Nat)
  : Sum.swap ∘ @sumLoHi m n = sumHiLo ∘ cast (Nat.add_comm m n)
  := funext sumLoHi_swap

theorem Fin.sumHiLo_swap {m n: Nat} (i: Fin (m + n))
  : i.sumHiLo.swap = (i.cast (Nat.add_comm m n)).sumLoHi := by
    simp only [
      sumLoHi, casesAdd, eq_rec_constant, sumHiLo, addCases,
      coe_cast, cast_trans, cast_eq_self]
    split <;> rfl

theorem Fin.swap_comp_sumHiLo (m n: Nat)
  : Sum.swap ∘ @sumHiLo m n = sumLoHi ∘ cast (Nat.add_comm m n)
  := funext sumHiLo_swap

theorem Fin.addNat_cast_natAdd {n: Nat} (i: Fin n) (k: Nat)
  : i.addNat k = (i.natAdd k).cast (by rw [Nat.add_comm])
  := by simp

theorem Fin.natAdd_cast_addNat {n: Nat} (i: Fin n) (k: Nat)
  : i.natAdd k = (i.addNat k).cast (by rw [Nat.add_comm])
  := by simp
