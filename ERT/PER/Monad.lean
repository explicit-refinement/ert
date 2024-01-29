import Mathlib.Logic.Nontrivial.Defs
import ERT.PER.Basic

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

-- theorem pure_naturality_square {T} [Monad T] [LawfulMonad T]
--   {α β} {x y: α} (f: α -> β)
--   : @pure T _ α x = @pure T _ α y -> @pure T _ β (f x) = @pure T _ β (f y)
--   := sorry

-- theorem exists_equalizing_function {α β} {x y: α} (Hxy: x ≠ y) (u v: β)
--   : ∃f: α -> β, f x = u ∧ f y = v
--   := ⟨
--     λz => open Classical in if x = z then u else v,
--     by simp,
--     by simp [Hxy]
--   ⟩

-- theorem pure_equates_pure_constant {T} [Monad T] [LawfulMonad T] {α β} {x y: α}
--   (Hxy: x ≠ y)
--   (Hpxy: @pure T _ α x = @pure T _ α y)
--   (u v: β)
--   : @pure T _ β u = @pure T _ β v :=
--     have ⟨f, fxu, fyv⟩ := exists_equalizing_function Hxy u v;
--     fxu ▸ fyv ▸ pure_naturality_square f Hpxy

-- theorem pure_monic {T} [Monad T] [LawfulMonad T] {α β} {f g: α -> T β}
--   : f >=> pure = g >=> pure -> f = g
--   := by
--     intro H
--     funext x
--     have H': (f >=> pure) x = (g >=> pure) x := by rw [H]
--     simp only [Bind.kleisliRight, bind_pure] at H'
--     exact H'

-- theorem pure_equates_function_constant {T} [Monad T] [LawfulMonad T] {α β} {x y: α}
--   (Hxy: x ≠ y)
--   (Hpxy: @pure T _ α x = @pure T _ α y)
--   (f g: β -> T β)
--   : f = g := pure_monic (by
--     funext x
--     simp only [Bind.kleisliRight]
--     sorry
--   )

-- theorem local_lawful_pure_injective_or_subsingleton {T} [Monad T] [LawfulMonad T]
--   : ∀α, Function.Injective (@pure T _ α) ∨ Subsingleton (T α)
--   | α => (subsingleton_or_nontrivial (T α)).elim
--     Or.inr
--     (λ⟨x, y, Hxy⟩ =>
--       have ⟨f, fxu, fyv⟩ := exists_equalizing_function Hxy x y
--       sorry)
