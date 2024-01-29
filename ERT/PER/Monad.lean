import Mathlib.Logic.Nontrivial.Defs
import ERT.PER.Basic

class Function.Constant {α β} (f: α -> β): Prop where
  allEq: ∀x y, f x = f y

def Relation.PureMap (r: α -> β -> Prop) (T) [Pure T]
  : T α -> T β -> Prop
  := Relation.Map r pure pure

def PER.pure_map {α} {r: α -> α -> Prop} (A: PER r) (T) [Pure T]
  (Hinj: ∀{α}, Function.Injective (@pure T _ α))
  : PER (Relation.PureMap r T) where
  symm | ⟨x, y, rxy, px, py⟩ => ⟨y, x, A.symm rxy, py, px⟩
  trans
    | ⟨x, y, rxy, px, py⟩, ⟨y', z, ryz, py', pz⟩ =>
      have Hyy': y = y' := Hinj (py' ▸ py)
      ⟨x, z, A.trans (Hyy' ▸ rxy) ryz, px, pz⟩

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
  {T} [Monad T] [LawfulMonad T] (α)
  : Function.Injective (@pure T _ α) ∨ Function.Constant (@pure T _ α)
  := open Classical in
  if H: Function.Injective (@pure T _ α)
  then Or.inl H
  else Or.inr ⟨constant_of_not_injective H⟩

theorem pure_injective_or_constant
  {T} [Monad T] [LawfulMonad T]
  : (∀α, Function.Injective (@pure T _ α))
  ∨ (∀α, Function.Constant (@pure T _ α))
  := open Classical in
  if H: ∀α, Function.Constant (@pure T _ α)
  then Or.inr H
  else Or.inl λβ =>
    if HI: Function.Injective (@pure T _ β)
    then HI
    else H.elim (λ_ => ⟨constant_of_not_injective HI⟩)
