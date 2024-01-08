import ERT.Typed.Basic

inductive WkCtx {α}: (Γ: List (Var α)) -> (Δ: List (Var α)) -> (ℕ -> ℕ) -> Type
  | nil (ρ): WkCtx [] [] ρ
  | lift (A): WkCtx Γ Δ ρ -> w'.le w →
    WkCtx (Var.mk (A.wk ρ) w :: Γ) (Var.mk A w' :: Δ) (liftWk ρ)
  | step (A): WkCtx Γ Δ ρ -> WkCtx (Var.mk A w :: Γ) Δ (stepWk ρ)

def WkCtx.slift {α Γ Δ ρ} (A w) (R: @WkCtx α Γ Δ ρ):
  WkCtx (Var.mk (A.wk ρ) w :: Γ) (Var.mk A w :: Δ) (liftWk ρ) :=
  WkCtx.lift _ R (World.le.refl _)

def WkCtx.src {α Γ Δ ρ} (_: @WkCtx α Γ Δ ρ): List (Var α) := Γ
def WkCtx.trg {α Γ Δ ρ} (_: @WkCtx α Γ Δ ρ): List (Var α) := Δ

def WkCtx.ix {α Γ Δ ρ} (_: @WkCtx α Γ Δ ρ): ℕ -> ℕ := ρ

def HasVar.wk {α Γ Δ ρ A n w}: @WkCtx α Γ Δ ρ -> HasVar Δ n A w -> HasVar Γ (ρ n) (A.wk ρ) w
  | WkCtx.lift _ ρ H', head _ _ H => Term.wk_lift_succ _ _ ▸ head _ _ (H.trans H')
  | WkCtx.lift _ ρ _, tail v => Term.wk_lift_succ _ _ ▸ tail (v.wk ρ)
  | WkCtx.step _ ρ, v => Term.wk_step_succ _ _ ▸ tail (v.wk ρ)

theorem Term.IsSort.fv_zero {α K w} (H: @IsSort α K w): K.fv = 0 := by cases H <;> rfl

theorem Term.IsSort.eq_wk {α K w} (H: @IsSort α K w) (ρ: _): K.wk ρ = K := K.wk_closed (H.fv_zero)

theorem Term.IsSort.eq_wk' {α K w} (H: @IsSort α K w) (ρ ρ': _): K.wk ρ = K.wk ρ' :=
  (H.eq_wk ρ).trans (H.eq_wk ρ').symm

def Term.IsSort.wk {α K w} (H: @IsSort α K w) (ρ: _): IsSort (K.wk ρ) w := (H.eq_wk _).symm ▸ H

def Term.HasType.wk {α Γ Δ ρ a A w} (R: @WkCtx α Γ Δ ρ)
  : HasType Δ a A w -> HasType Γ (a.wk ρ) (A.wk ρ) w
  | var v HA HS => var (v.wk R) (HA.wk R) (HS.wk ρ)
  | pi HA HKA HB HKB =>
    pi (HA.wk R) (HKA.wk ρ) ((HKB.eq_wk' _ _) ▸ HB.wk (R.slift _ _)) (HKB.wk ρ)
  | unit _ _ => unit _ _
  | nat _ _ => nat _ _
  | prop _ => prop _
  | top _ => top _
  | bot _ => bot _
  | eq HA Ha Hb => eq (HA.wk R) (Ha.wk R) (Hb.wk R)
  | lam HA HKA Ht HB => lam (HA.wk R) (HKA.wk ρ) (Ht.wk (R.slift _ _)) (HB.wk (R.slift _ _))
  | app Hs Ht E => app (Hs.wk R) (Ht.wk R) (E ▸ Term.subst0_liftWk _ _ _)
