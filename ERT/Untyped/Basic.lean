import ERT.Utils.Wk
import Mathlib.Order.MinMax
import Mathlib.Tactic.SolveByElim

inductive World
  | computation
  | ghost

inductive Kind
  | type (w: World)
  | prop

inductive Term (α: Type)
  -- Variables
  | var (n: Nat)

  -- Type/proposition formers
  | pi (k: Kind) (A B: Term α)
  | sigma (k: Kind) (A B: Term α)
  | coprod (A B: Term α)

  -- Base types
  | unit
  | nat
  | prop

  -- Base propositions
  | top
  | bot
  | eq (a b: Term α)

  -- Term/proof formers
  | let1 (a e: Term α)
  | lam (k: Kind) (A t: Term α)
  | app (s t: Term α)
  | pair (k: Kind) (s t: Term α)
  | let2 (a e: Term α)
  | inj (b: Fin 2) (t: Term α)
  | case (e l r: Term α)

  -- Term formers
  | nil
  | zero
  | succ
  | natrec (n z s: Term α)

  -- Proof formers
  | triv
  | abort

  -- General kind formers
  | type

  -- Axioms
  | refl
  | discr
  | unit_unique
  | cong
  | beta
  | beta_trans
  | beta_pr
  | beta_ir
  | beta_left
  | beta_right
  | beta_pair
  | beta_let2
  | beta_let1
  | eta
  | irir
  | prir

  -- Custom constants/axioms
  | extra (a: α)

def Term.fv {α}: Term α -> ℕ
  | var n => n.succ
  | pi _ A B | sigma _ A B => A.fv.max B.fv.pred
  | coprod A B => A.fv.max B.fv
  | eq a b => a.fv.max b.fv
  | let1 a e => a.fv.max e.fv.pred
  | lam _ A t => A.fv.max t.fv.pred
  | app s t => s.fv.max t.fv
  | pair _ s t => s.fv.max t.fv
  | let2 a e => a.fv.max e.fv.pred.pred
  | inj _ t => t.fv
  | case e l r => e.fv.max (l.fv.pred.max r.fv.pred)
  | natrec n z s => n.fv.max (z.fv.max s.fv.pred.pred)
  | _ => 0

def Term.wk {α} (ρ: ℕ -> ℕ): Term α -> Term α
  | var n => var (ρ n)
  | pi k A B => pi k (A.wk ρ) (B.wk (liftWk ρ))
  | sigma k A B => sigma k (A.wk ρ) (B.wk (liftWk ρ))
  | coprod A B => coprod (A.wk ρ) (B.wk ρ)
  | eq a b => eq (a.wk ρ) (b.wk ρ)
  | let1 a e => let1 (a.wk ρ) (e.wk (liftWk ρ))
  | lam k A t => lam k (A.wk ρ) (t.wk (liftWk ρ))
  | app s t => app (s.wk ρ) (t.wk ρ)
  | pair k s t => pair k (s.wk ρ) (t.wk ρ)
  | let2 a e => let2 (a.wk ρ) (e.wk (liftWk (liftWk ρ)))
  | inj b t => inj b (t.wk ρ)
  | case e l r => case (e.wk ρ) (l.wk (liftWk ρ)) (r.wk (liftWk ρ))
  | natrec n z s => natrec (n.wk ρ) (z.wk ρ) (s.wk (liftWk (liftWk ρ)))
  | t => t

theorem Term.wk_id {α} (t: Term α): t.wk id = t := by
  induction t with
  | var _ => rfl
  | _ => simp only [Term.wk, liftWk_id, *]

theorem Term.wk_comp {α} (ρ σ: ℕ -> ℕ) (t: Term α):
  t.wk (ρ ∘ σ) = (t.wk σ).wk ρ := by
  induction t generalizing ρ σ with
  | var _ => rfl
  | _ => simp only [Term.wk, liftWk_comp, *]

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
