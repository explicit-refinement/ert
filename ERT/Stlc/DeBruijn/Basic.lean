import ERT.Stlc.Basic
import ERT.Utils.Wk
import Mathlib.Order.MinMax

namespace Stlc.DeBruijn

inductive Term (α: Type): Type
  | var (n: Nat)
  | app (s t: Term α)
  | lam (A: Ty) (t: Term α)
  | pair (s t: Term α)
  | let2 (s t: Term α)
  | case (e l r: Term α)
  | inj (b: Fin 2) (t: Term α)
  | cnst (a: α)
  | abort (A: Ty)

def Term.wk {α} (ρ: Nat -> Nat) : Term α -> Term α
  | var n => var (ρ n)
  | app s t => app (wk ρ s) (wk ρ t)
  | lam A t => lam A (wk (liftWk ρ) t)
  | pair s t => pair (wk ρ s) (wk ρ t)
  | let2 s t => let2 (wk ρ s) (wk (liftWk (liftWk ρ)) t)
  | case e l r => case (wk ρ e) (wk (liftWk ρ) l) (wk (liftWk ρ) r)
  | inj b t => inj b (wk ρ t)
  | t => t

theorem Term.wk_id {α} (t: Term α): t.wk id = t := by
  induction t with
  | var _ => rfl
  | _ => simp only [Term.wk, liftWk_id, *]

theorem Term.wk_id' {α} (t: Term α): t.wk (λx => x) = t := t.wk_id

theorem Term.wk_comp {α} (ρ σ: ℕ -> ℕ) (t: Term α):
  t.wk (ρ ∘ σ) = (t.wk σ).wk ρ := by
  induction t generalizing ρ σ with
  | var _ => rfl
  | _ => simp only [Term.wk, liftWk_comp, *]

theorem Term.wk_lift_succ {α} (ρ: ℕ -> ℕ) (t: Term α):
  (t.wk Nat.succ).wk (liftWk ρ) = (t.wk ρ).wk Nat.succ := by
  rw [<-Term.wk_comp]
  rw [liftWk_comp_succ]
  rw [Term.wk_comp]

theorem Term.wk_step_succ {α} (ρ: ℕ -> ℕ) (t: Term α):
  (t.wk ρ).wk Nat.succ = t.wk (stepWk ρ) := by
  rw [<-Term.wk_comp]
  rfl

def Term.fv {α}: Term α -> ℕ
  | var n => n.succ
  | lam _ t => t.fv.pred
  | app s t => s.fv.max t.fv
  | pair s t => s.fv.max t.fv
  | let2 a e => a.fv.max e.fv.pred.pred
  | inj _ t => t.fv
  | case e l r => e.fv.max (l.fv.pred.max r.fv.pred)
  | _ => 0

theorem Term.wk_fv {α ρ σ} (t: Term α) (H: EqToN t.fv ρ σ): t.wk ρ = t.wk σ := by
  induction t generalizing ρ σ with
  | var n => exact congrArg _ (H n (Nat.le_refl n.succ))
  | _ =>
    simp only [Term.wk] <;>
    simp only [Term.fv] at H
    repeat apply congr
    all_goals first
      | rfl
      | {
        apply_assumption
        repeat apply liftWk_eqToN_pred
        apply H.le_sub
        simp [le_max_iff, le_refl, true_or]
      }

theorem Term.wk_closed {α ρ} (t: Term α) (H: t.fv = 0): t.wk ρ = t :=
  (t.wk_fv (H.symm ▸ (EqToN.zero_app _ id))).trans t.wk_id

def Subst (α: Type) := ℕ -> Term α

def Subst.id (α: Type): Subst α := Term.var

def Subst.lift {α} (σ: Subst α): Subst α
  | 0 => Term.var 0
  | n+1 => (σ n).wk Nat.succ

def Subst.liftn {α} (n: ℕ) (σ: Subst α): Subst α
  | m => if m < n then Term.var m else (σ (m - n)).wk (λv => v + n)

def Subst.liftn_zero {α} (σ: Subst α): σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).wk_id
def Subst.liftn_succ {α} (n) (σ: Subst α): σ.liftn n.succ = (σ.liftn n).lift := by
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

def Subst.liftn_eq_iterate_lift {α} (n: ℕ) (σ: Subst α): σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n I => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

def Subst.lift_zero {α} (σ: Subst α): σ.lift 0 = Term.var 0 := rfl
def Subst.lift_succ {α} (σ: Subst α) (n): (σ.lift n.succ) = (σ n).wk Nat.succ := rfl

def Subst.lift_id (α): (id α).lift = id α := by funext n; cases n <;> rfl

def Term.subst {α} (σ: Subst α): Term α -> Term α
  | var n => σ n
  | app s t => app (subst σ s) (subst σ t)
  | lam A t => lam A (subst σ.lift t)
  | pair s t => pair (subst σ s) (subst σ t)
  | let2 a e => let2 (subst σ a) (subst σ.lift.lift e)
  | inj b t => inj b (subst σ t)
  | case e l r => case (subst σ e) (subst σ.lift l) (subst σ.lift r)
  | t => t

def Term.subst_id {α} (t: Term α): t.subst (Subst.id α) = t := by
  induction t with
  | var _ => rfl
  | _ => simp only [Term.subst, Subst.lift_id, *]



def Subst.fromWk (α) (ρ: ℕ -> ℕ): Subst α := Term.var ∘ ρ

theorem Subst.fromWk_lift (α ρ): (fromWk α ρ).lift = fromWk α (liftWk ρ) := by
  funext n; cases n <;> rfl

theorem Term.subst_wk {α} (ρ: ℕ -> ℕ) (t: Term α): t.subst (Subst.fromWk α ρ) = t.wk ρ := by
  induction t generalizing ρ with
  | var n => rfl
  | _ => simp only [Term.subst, Term.wk, Subst.fromWk_lift, *]

theorem Term.subst_liftWkn {α} (t: Term α) (σ: Subst α) (n)
  : (t.wk (liftWk^[n] Nat.succ)).subst (Subst.lift^[n + 1] σ)
  = (t.subst (Subst.lift^[n] σ)).wk (liftWk^[n] Nat.succ) := by
  induction t generalizing σ n with
  | var v =>
    simp only [
      <-liftnWk_eq_iterate_liftWk,
      <-Subst.liftn_eq_iterate_lift,
      wk, subst, liftnWk, Subst.liftn
    ]
    split
    . split
      . simp [wk, liftnWk, *]
      . rename_i H C; exact (C (Nat.le_step H)).elim
    . rename_i C
      simp_arith only [ite_false, <-wk_comp]
      apply congr
      . apply congrArg
        funext v
        simp_arith [Function.comp_apply, liftnWk]
      . simp [Nat.succ_add, Nat.succ_sub_succ, Nat.add_sub_assoc]
  | _ => simp only [Term.subst, Term.wk, <-Function.iterate_succ_apply', *]

theorem Term.subst_lift {α} (t: Term α) (σ: Subst α)
  : (t.wk Nat.succ).subst (σ.lift) = (t.subst σ).wk Nat.succ := t.subst_liftWkn σ 0

def Subst.comp {α} (σ τ: Subst α): Subst α
  | n => (τ n).subst σ

theorem Subst.lift_comp {α} (σ τ: Subst α): (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [lift, comp, Term.subst_lift]

theorem Term.subst_comp {α} (σ τ: Subst α) (t: Term α)
  : t.subst (σ.comp τ) = (t.subst τ).subst σ := by
  induction t generalizing σ τ with
  | var n => rfl
  | _ => simp only [Term.subst, Subst.lift_comp, *]

theorem Subst.lift_eqToN_succ {α} {σ τ: Subst α} {n} (H: EqToN n σ τ): EqToN n.succ σ.lift τ.lift
  | 0, _ => rfl
  | m + 1, Hm => congrArg _ (H m (Nat.lt_of_succ_lt_succ Hm))

theorem Subst.lift_congr_eqToN {α} {σ τ: Subst α} {n} (H: EqToN n σ τ)
  : EqToN n σ.lift τ.lift := (lift_eqToN_succ H).succ_sub

theorem Subst.lift_eqToN_pred {α} {σ τ: Subst α} {n}: EqToN n.pred σ τ -> EqToN n σ.lift τ.lift :=
  match n with | 0 => lift_congr_eqToN | _ + 1 => lift_eqToN_succ

theorem Term.subst_fv {α σ τ} (t: Term α) (H: EqToN t.fv σ τ): t.subst σ = t.subst τ := by
  induction t generalizing σ τ with
  | var n =>  exact H n (Nat.le_refl n.succ)
  | _ =>
    simp only [Term.subst] <;>
    simp only [Term.fv] at H
    repeat apply congr
    all_goals first
      | rfl
      | {
        apply_assumption
        repeat apply Subst.lift_eqToN_pred
        apply H.le_sub
        simp [le_max_iff, le_refl, true_or]
      }

theorem Term.subst_closed {α σ} (t: Term α) (H: t.fv = 0): t.subst σ = t :=
  (t.subst_fv (H.symm ▸ (EqToN.zero_app _ _))).trans t.subst_id

def Term.subst0 {α} (t: Term α): Subst α
  | 0 => t
  | n + 1 => var n

def Term.alpha0 {α} (t: Term α): Subst α
  | 0 => t
  | n => var n

theorem Term.subst0_liftn_liftWk_liftn {α} (t: Term α) (ρ: ℕ -> ℕ) (s: Term α) (n)
  : (t.wk (liftWk^[n + 1] ρ)).subst (Subst.lift^[n] (s.wk ρ).subst0)
  = (t.subst (Subst.lift^[n] s.subst0)).wk (liftWk^[n] ρ) := by
  induction t generalizing ρ s n with
  | var v =>
    simp only [
      subst, wk,
      <-Subst.liftn_eq_iterate_lift,
      <-liftnWk_eq_iterate_liftWk,
      Subst.liftn, liftnWk
    ]
    split
    . split
      . simp_arith [wk, liftnWk, *]
      . rename_i H C
        have H: v = n := by
          cases H
          rfl
          contradiction
        cases H
        simp only [subst0, Nat.sub_self, ←wk_comp]
        congr
        funext _
        simp [liftnWk]
        split <;> simp_arith at *
    . split
      . simp_arith at *
      . split
        . rename_i C _ H
          exact (C (Nat.lt_succ_of_lt H)).elim
        . simp only [subst0]
          split
          . rename_i H _ _ He
            have He := Nat.le_of_sub_eq_zero He
            have He' := not_lt_of_le He
            cases Nat.eq_or_lt_of_not_lt H with
            | inl H => cases H
            | inr H => contradiction
          . rename_i Hv H _ _ _ He
            cases Nat.eq_or_lt_of_not_lt H with
            | inl H => cases H
            | inr H =>
              split
              . rename_i He
                exact (Hv (Nat.lt_succ_of_le (Nat.le_of_sub_eq_zero He))).elim
              . simp_arith only [wk, liftnWk, Nat.add_sub_cancel, var.injEq, ite_false]
                rw [Nat.add_sub_assoc (Nat.le_succ _)] at He
                rw [Nat.succ_sub] at He
                rw [Nat.sub_self] at He
                cases He
                rw [Nat.sub_succ, Nat.add]
                simp_arith [*]
                exact le_refl _
  | _ => simp only [subst, wk, <-Function.iterate_succ_apply', *]

theorem Term.subst0_liftWk {α} (t: Term α) (ρ: ℕ -> ℕ) (s: Term α)
  : (t.wk (liftWk ρ)).subst (s.wk ρ).subst0 = (t.subst s.subst0).wk ρ :=
  subst0_liftn_liftWk_liftn t ρ s 0

-- TODO: just make this a prop or smt...

inductive Var : Ctx -> Nat -> Ty -> Type
| head : Var (A :: Γ) 0 A
| tail : Var Γ n A -> Var (B :: Γ) (n + 1) A

-- TODO: HasTy

-- TODO: Subst

-- TODO: Iso w/ Intrinsic? In another file?
