import Mathlib.Logic.Relation
import Mathlib.Init.Function

def Relation.SymmGen {α : Type u} (r : α → α → Prop) : α → α → Prop := λa b => r a b ∨ r b a

theorem Relation.SymmGen.symmetric {α} {r: α -> α -> Prop}: Symmetric (SymmGen r)
  := λ_ _ H => H.elim Or.inr Or.inl

theorem Relation.symmGen_eq_self {α} {r : α → α → Prop} (Hr: Symmetric r): Relation.SymmGen r = r
  := funext₂ (λ_ _ => propext ⟨λH => H.elim id (λp => Hr p), Or.inl⟩)

theorem Relation.TransGen.symmetric {α} {r: α -> α -> Prop} (Hr: Symmetric r)
  : Symmetric (Relation.TransGen r) := by
  intro a b H
  induction H with
  | single H => exact (single $ Hr H)
  | tail _ H' I => exact (trans (single $ Hr H') I)

theorem Symmetric.map {α β} {r: α -> α -> Prop} (Hr: Symmetric r) (f: α -> β)
  : Symmetric (Relation.Map r f f)
  := λ _ _ ⟨a₁, a₂, Ha₁a₂, Ha₁, Ha₂⟩ => ⟨a₂, a₁, Hr Ha₁a₂, Ha₂, Ha₁⟩

theorem Function.Injective.transitive {α β} {r: α -> α -> Prop} {f: α -> β}
  (Hf: Function.Injective f) (Hr: Transitive r) : Transitive (Relation.Map r f f)
  := λ _ _ _ ⟨a₁, _, Ha₁a₂, Ha₁, Ha₂⟩ ⟨_, a₃, Ha₂'a₃, Ha₂', Ha₃⟩ =>
    ⟨a₁, a₃, Hr Ha₁a₂ (Hf (Ha₂.trans Ha₂'.symm) ▸ Ha₂'a₃), Ha₁, Ha₃⟩

class Function.Constant {α β} (f: α -> β): Prop where
  allEq: ∀x y, f x = f y

theorem Function.Constant.symmetric {α β} {f: α -> β} (Hf: Constant f) (r: α -> α -> Prop)
  : Symmetric (Relation.Map r f f)
  := λ _ _ ⟨a₁, a₂, _, Ha₁, Ha₂⟩ => by
    cases Ha₁
    cases Ha₂
    rw [Hf.allEq a₁ a₂] at *
    assumption

theorem Function.Constant.transitive {α β} {f: α -> β} (Hf: Constant f) (r: α -> α -> Prop)
  : Transitive (Relation.Map r f f)
  := λ _ _ _ ⟨a₁, a₂, _, Ha₁, Ha₂⟩ ⟨_, a₃, _, _, Ha₃⟩ => by
    cases Ha₁
    cases Ha₂
    cases Ha₃
    rw [Hf.allEq a₁ a₂] at *
    assumption

def Relation.PureMap (r: α -> β -> Prop) (T) [Pure T]
  : T α -> T β -> Prop
  := Relation.Map r pure pure

theorem pure_naturality_square {T} [Monad T] [LawfulMonad T]
  {α β} {x y: α} (f: α -> β) (H: @pure T _ α x = @pure T _ α y)
  : @pure T _ β (f x) = @pure T _ β (f y)
  := by
    rw [<-bind_pure (pure (f x))]
    rw [<-bind_pure (pure (f y))]
    rw [pure_bind, pure_bind]
    rw [<-map_pure, <-map_pure]
    rw [H]

theorem exists_equalizing_function {α β} {x y: α} (Hxy: x ≠ y) (u v: β)
  : ∃f: α -> β, f x = u ∧ f y = v
  := ⟨
    λz => open Classical in if x = z then u else v,
    by simp,
    by simp [Hxy]
  ⟩

theorem constant_of_pure_equates {T} [Monad T] [LawfulMonad T]
  {α β} {x y: α}
  (Hxy: x ≠ y)
  (Hpxy: @pure T _ α x = @pure T _ α y)
  (u v: β)
  : @pure T _ β u = @pure T _ β v :=
    have ⟨f, fxu, fyv⟩ := exists_equalizing_function Hxy u v;
    fxu ▸ fyv ▸ pure_naturality_square f Hpxy

theorem constant_of_not_injective {T} [Monad T] [LawfulMonad T]
  {α β} (Hf: ¬Function.Injective (@pure T _ α))
  : (u v: β) -> @pure T _ β u = @pure T _ β v
  :=
    open Classical in
    if H: ∃x y, x ≠ y ∧ @pure T _ α x = @pure T _ α y
    then
      have ⟨_x, _y, Hxy, Hpxy⟩ := H
      constant_of_pure_equates Hxy Hpxy
    else
      (Hf (λx y Hpxy =>
        if Hxy: x = y then
          Hxy
        else
          (H ⟨x, y, Hxy, Hpxy⟩).elim
        )).elim

theorem local_pure_injective_or_constant
  (T) [Monad T] [LawfulMonad T] (α)
  : Function.Injective (@pure T _ α) ∨ Function.Constant (@pure T _ α)
  := open Classical in
  if H: Function.Injective (@pure T _ α)
  then Or.inl H
  else Or.inr ⟨constant_of_not_injective H⟩

theorem pure_injective_or_constant
  (T) [Monad T] [LawfulMonad T]
  : (∀α, Function.Injective (@pure T _ α))
  ∨ (∀α, Function.Constant (@pure T _ α))
  := open Classical in
  if H: ∀α, Function.Constant (@pure T _ α)
  then Or.inr H
  else Or.inl λβ =>
    if HI: Function.Injective (@pure T _ β)
    then HI
    else H.elim (λ_ => ⟨constant_of_not_injective HI⟩)

theorem Symmetric.pure_map {α} {r: α -> α -> Prop} (Hr: Symmetric r) (T) [Pure T]
  : Symmetric (Relation.PureMap r T)
  := λ _ _ ⟨a₁, a₂, Ha₁a₂, Ha₁, Ha₂⟩ => ⟨a₂, a₁, Hr Ha₁a₂, Ha₂, Ha₁⟩

theorem Transitive.pure_map {α} {r: α -> α -> Prop} (Hr: Transitive r) (T) [Monad T] [LawfulMonad T]
  : Transitive (Relation.PureMap r T)
  := match pure_injective_or_constant T with
  | Or.inl H => (H α).transitive Hr
  | Or.inr H => (H α).transitive r
