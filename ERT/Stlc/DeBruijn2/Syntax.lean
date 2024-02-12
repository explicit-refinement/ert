import ERT.Stlc.Basic
import ERT.Utils.Wk
import Mathlib.Order.MinMax

namespace Stlc.DeBruijn2

inductive BaseTy
| unit
| nat

instance: Semantic BaseTy where
  coe
  | BaseTy.unit => Unit
  | BaseTy.nat => Nat
  Effect := Option
  isMonad := inferInstance
  isLawful := inferInstance
  abort := @none

inductive Term: Type
  | var (n: Nat)
  | app (s t: Term)
  | lam (A: Ty BaseTy) (t: Term)
  | pair (s t: Term)
  | let1 (s t: Term)
  | let2 (s t: Term)
  | case (e l r: Term)
  | inj (b: Fin 2) (t: Term)
  | zero
  | succ (t: Term)
  | natrec (z s n: Term)
  | abort (A: Ty BaseTy)

def Term.wk (ρ: Nat -> Nat) : Term -> Term
  | var n => var (ρ n)
  | app s t => app (wk ρ s) (wk ρ t)
  | lam A t => lam A (wk (liftWk ρ) t)
  | pair s t => pair (wk ρ s) (wk ρ t)
  | let1 s t => let1 (wk ρ s) (wk (liftWk ρ) t)
  | let2 s t => let2 (wk ρ s) (wk (liftWk (liftWk ρ)) t)
  | case e l r => case (wk ρ e) (wk (liftWk ρ) l) (wk (liftWk ρ) r)
  | inj b t => inj b (wk ρ t)
  | succ s => succ (wk ρ s)
  | natrec z s n => natrec (wk ρ z) (wk (liftWk (liftWk ρ)) s) (wk ρ n)
  | t => t

theorem Term.wk_id (t: Term): t.wk id = t := by
  induction t with
  | var _ => rfl
  | _ => simp only [Term.wk, liftWk_id, *]

theorem Term.wk_id' (t: Term): t.wk (λx => x) = t := t.wk_id

theorem Term.wk_comp (ρ σ: ℕ -> ℕ) (t: Term):
  t.wk (ρ ∘ σ) = (t.wk σ).wk ρ := by
  induction t generalizing ρ σ with
  | var _ => rfl
  | _ => simp only [Term.wk, liftWk_comp, *]

theorem Term.wk_lift_succ (ρ: ℕ -> ℕ) (t: Term):
  (t.wk Nat.succ).wk (liftWk ρ) = (t.wk ρ).wk Nat.succ := by
  rw [<-Term.wk_comp]
  rw [liftWk_comp_succ]
  rw [Term.wk_comp]

theorem Term.wk_step_succ (ρ: ℕ -> ℕ) (t: Term):
  (t.wk ρ).wk Nat.succ = t.wk (stepWk ρ) := by
  rw [<-Term.wk_comp]
  rfl

def Term.fv: Term -> ℕ
  | var n => n.succ
  | lam _ t => t.fv.pred
  | app s t => s.fv.max t.fv
  | pair s t => s.fv.max t.fv
  | let1 a e => a.fv.max e.fv.pred
  | let2 a e => a.fv.max e.fv.pred.pred
  | inj _ t => t.fv
  | case e l r => e.fv.max (l.fv.pred.max r.fv.pred)
  | succ t => t.fv
  | natrec z s n => z.fv.max (s.fv.pred.pred.max n.fv)
  | _ => 0

theorem Term.wk_fv {ρ σ} (t: Term) (H: EqToN t.fv ρ σ): t.wk ρ = t.wk σ := by
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

theorem Term.wk_closed {ρ} (t: Term) (H: t.fv = 0): t.wk ρ = t :=
  (t.wk_fv (H.symm ▸ (EqToN.zero_app _ id))).trans t.wk_id

def Subst := ℕ -> Term

def Subst.id: Subst := Term.var

def Subst.lift (σ: Subst): Subst
  | 0 => Term.var 0
  | n+1 => (σ n).wk Nat.succ

def Subst.liftn (n: ℕ) (σ: Subst): Subst
  | m => if m < n then Term.var m else (σ (m - n)).wk (λv => v + n)

def Subst.liftn_zero (σ: Subst): σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).wk_id
def Subst.liftn_succ (n) (σ: Subst)
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

def Subst.liftn_eq_iterate_lift (n: ℕ) (σ: Subst)
  : σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n I => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

def Subst.lift_zero (σ: Subst): σ.lift 0 = Term.var 0 := rfl
def Subst.lift_succ (σ: Subst) (n)
  : (σ.lift n.succ) = (σ n).wk Nat.succ := rfl

def Subst.lift_id: id.lift = id := by funext n; cases n <;> rfl

def Term.subst (σ: Subst): Term -> Term
  | var n => σ n
  | app s t => app (subst σ s) (subst σ t)
  | lam A t => lam A (subst σ.lift t)
  | pair s t => pair (subst σ s) (subst σ t)
  | let1 a e => let1 (subst σ a) (subst σ.lift e)
  | let2 a e => let2 (subst σ a) (subst σ.lift.lift e)
  | inj b t => inj b (subst σ t)
  | case e l r => case (subst σ e) (subst σ.lift l) (subst σ.lift r)
  | succ s => succ (subst σ s)
  | natrec z s n => natrec (subst σ z) (subst σ.lift.lift s) (subst σ n)
  | t => t

def Term.subst_id (t: Term): t.subst (Subst.id) = t := by
  induction t with
  | var _ => rfl
  | _ => simp only [Term.subst, Subst.lift_id, *]

def Subst.fromWk (ρ: ℕ -> ℕ): Subst := Term.var ∘ ρ

theorem Subst.fromWk_lift (ρ): (fromWk ρ).lift = fromWk (liftWk ρ) := by
  funext n; cases n <;> rfl

theorem Term.subst_wk (ρ: ℕ -> ℕ) (t: Term)
  : t.subst (Subst.fromWk ρ) = t.wk ρ := by
  induction t generalizing ρ with
  | var n => rfl
  | _ => simp only [Term.subst, Term.wk, Subst.fromWk_lift, *]

theorem Term.subst_liftWkn (t: Term) (σ: Subst) (n)
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

theorem Term.subst_lift (t: Term) (σ: Subst)
  : (t.wk Nat.succ).subst (σ.lift) = (t.subst σ).wk Nat.succ := t.subst_liftWkn σ 0

def Subst.comp (σ τ: Subst): Subst
  | n => (τ n).subst σ

theorem Subst.lift_comp (σ τ: Subst): (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [lift, comp, Term.subst_lift]

theorem Term.subst_comp (σ τ: Subst) (t: Term)
  : t.subst (σ.comp τ) = (t.subst τ).subst σ := by
  induction t generalizing σ τ with
  | var n => rfl
  | _ => simp only [Term.subst, Subst.lift_comp, *]

theorem Subst.lift_eqToN_succ {σ τ: Subst} {n} (H: EqToN n σ τ)
  : EqToN n.succ σ.lift τ.lift
  | 0, _ => rfl
  | m + 1, Hm => congrArg _ (H m (Nat.lt_of_succ_lt_succ Hm))

theorem Subst.lift_congr_eqToN {σ τ: Subst} {n} (H: EqToN n σ τ)
  : EqToN n σ.lift τ.lift := (lift_eqToN_succ H).succ_sub

theorem Subst.lift_eqToN_pred {σ τ: Subst} {n}
  : EqToN n.pred σ τ -> EqToN n σ.lift τ.lift :=
  match n with | 0 => lift_congr_eqToN | _ + 1 => lift_eqToN_succ

theorem Term.subst_fv {σ τ: Subst} (t: Term) (H: EqToN t.fv σ τ)
  : t.subst σ = t.subst τ := by
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

theorem Term.subst_closed {σ} (t: Term) (H: t.fv = 0)
  : t.subst σ = t :=
  (t.subst_fv (H.symm ▸ (EqToN.zero_app _ _))).trans t.subst_id

def Term.subst0 (t: Term): Subst
  | 0 => t
  | n + 1 => var n

def Term.alpha0 (t: Term): Subst
  | 0 => t
  | n => var n

theorem Term.subst0_liftn_liftWk_liftn (t: Term) (ρ: ℕ -> ℕ) (s: Term) (n)
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

theorem Term.subst0_liftWk (t: Term) (ρ: ℕ -> ℕ) (s: Term)
  : (t.wk (liftWk ρ)).subst (s.wk ρ).subst0 = (t.subst s.subst0).wk ρ :=
  subst0_liftn_liftWk_liftn t ρ s 0
