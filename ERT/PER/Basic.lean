import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relator
import Mathlib.Order.CompleteLattice

import ERT.Utils.Relation

structure PER {α} (r: α -> α -> Prop): Prop where
  symm: ∀{x y: α}, r x y -> r y x
  trans: ∀{x y z: α}, r x y -> r y z -> r x z

def PER.eq {α}: PER (@Eq α) where
  symm := Eq.symm
  trans := Eq.trans
def PER.univ {α}: @PER α ⊤ where
  symm _ := True.intro
  trans _ _ := True.intro
def PER.empty {α}: @PER α ⊥ where
  symm := id
  trans _ := id

def PER.inf {α} {r s: α -> α -> Prop} (R: PER r) (S: PER s): PER (r ⊓ s) where
  symm H := ⟨R.symm H.left, S.symm H.right⟩
  trans H H' := ⟨R.trans H.left H'.left, S.trans H.right H'.right⟩

def PER.sInf {α: Type} {rs: Set (α -> α -> Prop)} (R: ∀r ∈ rs, PER r): PER (sInf rs) where
  symm
  | H, φ, ⟨⟨ra, r, Hra⟩, Hφ⟩ => by
    --TODO: clean this once I actually understand how the mathlib APIs work
    simp only [<-Hφ, <-Hra]
    apply (R r.1 r.2).symm
    rw [sInf_apply, iInf_apply] at H
    apply H
    apply Set.mem_range.mp ⟨r, by simp only []⟩
  trans
  | H, H', φ, ⟨⟨ra, r, Hra⟩, Hφ⟩ => by
    --TODO: clean this once I actually understand how the mathlib APIs work
    rename_i x y z
    simp only [<-Hφ, <-Hra]
    apply (R r.1 r.2).trans
    apply H
    apply Set.mem_range.mp ⟨⟨ra, r, Hra⟩, _⟩
    exact y
    simp only [<-Hra]
    apply H'
    apply Set.mem_range.mp ⟨⟨r.1 y, r, rfl⟩, _⟩
    simp

theorem PER.refl_left (A: PER r) (Hab: r a b): r a a
  := A.trans Hab (A.symm Hab)

theorem PER.refl_right (A: PER r) (Hab: r a b): r b b
  := A.trans (A.symm Hab) Hab

theorem PER.of_rel_subsingleton (r: α -> α -> Prop) (Hr: ∀{x y}, r x y -> x = y): PER r
  where
  symm Hxy := Hr Hxy ▸ Hr Hxy ▸ Hxy
  trans Hxy Hyz := Hr Hxy ▸ Hyz

theorem PER.of_subsingleton [S: Subsingleton α] (r: α -> α -> Prop): PER r
  := PER.of_rel_subsingleton r (λ_ => S.allEq _ _)

def PER.carrier {α} {r: α -> α -> Prop} (_: PER r)
  : Set α := λx: α => r x x

def PER.lift_fun {α β} {r: α -> α -> Prop} {s: β -> β -> Prop}
  (A: PER r) (B: PER s): PER (Relator.LiftFun r s) where
  symm Hxy _ _ Haa' := B.symm (Hxy (A.symm Haa'))
  trans Hrsxy Hrsyz _ _ Hraa' :=
    have Hraa := A.refl_left Hraa'
    have Hsxaya := Hrsxy Hraa
    have Hsyaza' := Hrsyz Hraa';
    B.trans Hsxaya Hsyaza'

def CRelToRel
  (r: α -> α -> Prop)
  (s: α -> β -> β -> Prop)
  : ((a: α) -> β) -> ((a: α) -> β) -> Prop
  := λf g => ∀{a a': α}, r a a' -> s a (f a) (g a')

-- def PER.c_rel_to_rel {α β} {r: α -> α -> Prop} {s: α -> β -> β -> Prop}
--   (A: PER r)
--   (B: ∀a, PER (s a))
--   (Hs: ∀{a a': α}, r a a' -> s a = s a')
--   : PER (CRelToRel r s) where
--   symm Hab _ _ Haa' := sorry
--   trans Hrsxy Hrsyz _ _ Hraa' := sorry

def DRelToRel
  (r: α -> α -> Prop)
  (β: α -> Type _)
  (s: (a: α) -> (a': α) -> β a -> β a' -> Prop)
  : ((a: α) -> β a) -> ((a: α) -> β a) -> Prop
  := λf g => ∀{a a': α}, r a a' -> s a a' (f a) (g a')

def CDRelToRel
  (r: α -> α -> Prop)
  (β: α -> Type _)
  (Hβ: ∀{a a': α}, r a a' -> β a = β a')
  (s: (a: α) -> β a -> β a -> Prop)
  : ((a: α) -> β a) -> ((a: α) -> β a) -> Prop
  := λf g => ∀{a a': α}, (H: r a a') -> s a (f a) (Hβ H ▸ (g a'))

theorem Equivalence.toPER {α} {r: α -> α -> Prop}
  (E: Equivalence r): PER r where
  symm := E.symm
  trans := E.trans

theorem PER.refl_equivalence {α} {r: α -> α -> Prop}
  (P: PER r) (refl: ∀x, r x x)
  : Equivalence r where
  refl := refl
  symm := P.symm
  trans := P.trans

class PSetoid (α: Type u) where
  r: α -> α -> Prop
  isper: PER r

theorem PSetoid.ext' {α} (S T: PSetoid α)
  (H: S.r = T.r)
  : S = T := match S, T with
  | ⟨r, _⟩, ⟨r', _⟩ => by
    subst H
    rfl

theorem PSetoid.ext {α} (S T: PSetoid α)
  (H: ∀a b, S.r a b ↔ T.r a b)
  : S = T := ext' S T (funext (λa => funext (λb => propext (H a b))))

instance {α}: LE (PSetoid α) where
  le S T := S.r ≤ T.r

theorem PSetoid.le_ext {α} (S T: PSetoid α)
  (H: S.r ≤ T.r): S ≤ T := H

instance {α}: PartialOrder (PSetoid α) where
  le_refl _ := PSetoid.le_ext _ _ (le_refl _)
  le_trans _ _ _ H H' := PSetoid.le_ext _ _ (le_trans H H')
  le_antisymm _ _ H H' := PSetoid.ext' _ _ (le_antisymm H H')

instance {α}: InfSet (PSetoid α) where
  sInf Ps := ⟨
    sInf ((λP => P.r) <$> Ps),
    PER.sInf (λ_ ⟨P, _, HPr⟩ => HPr ▸ P.isper)
  ⟩

def PSetoid.isGLB_sInf {α} (PS: Set (PSetoid α)): IsGLB PS (sInf PS) := ⟨
    λP HP => PSetoid.le_ext _ _ (CompleteLattice.sInf_le _ _ ⟨P, HP, rfl⟩),
    λ_ HP => PSetoid.le_ext _ _ (CompleteLattice.le_sInf _ _ (λ_ ⟨_, HP', He⟩ => He ▸ HP HP'))
  ⟩

instance {α}: CompleteLattice (PSetoid α) := {
  inf := λS T => ⟨S.r ⊓ T.r, PER.inf S.isper T.isper⟩,
  inf_le_left := λ_ _ => PSetoid.le_ext _ _ (inf_le_left),
  inf_le_right := λ_ _ => PSetoid.le_ext _ _ (inf_le_right),
  le_inf := λ_ _ _ H H' => PSetoid.le_ext _ _ (le_inf H H'),
  top := ⟨⊤, PER.univ⟩,
  le_top := λ_ => PSetoid.le_ext _ _ (le_top),
  bot := ⟨⊥, PER.empty⟩,
  bot_le := λ_ => PSetoid.le_ext _ _ (bot_le),
  sup := λ a b => sInf { x : PSetoid α | a ≤ x ∧ b ≤ x }
  sup_le := λ a b c hac hbc => (PSetoid.isGLB_sInf _).1 <| by simp [*]
  le_sup_left := λ a b => (PSetoid.isGLB_sInf _).2 λ x => And.left
  le_sup_right := λ a b => (PSetoid.isGLB_sInf _).2 λ x => And.right
  le_sInf := λ s a ha => (PSetoid.isGLB_sInf s).2 ha
  sInf_le := λ s a ha => (PSetoid.isGLB_sInf s).1 ha
  sSup := λ s => sInf (upperBounds s),
  le_sSup := λ s a ha => (PSetoid.isGLB_sInf (upperBounds s)).2 λ b hb => hb ha,
  sSup_le := λ s a ha => (PSetoid.isGLB_sInf (upperBounds s)).1 ha
}

instance {α: Type u} [PSetoid α] : HasEquiv α :=
  ⟨PSetoid.r⟩

theorem PSetoid.symm {α} [PSetoid α] {a b: α}: a ≈ b -> b ≈ a :=
  PSetoid.isper.symm

theorem PSetoid.trans {α} [PSetoid α] {a b c: α}: a ≈ b -> b ≈ c -> a ≈ c :=
  PSetoid.isper.trans

theorem PSetoid.refl_left {α} [PSetoid α] {a b: α}: a ≈ b -> a ≈ a :=
  PSetoid.isper.refl_left

theorem PSetoid.refl_right {α} [PSetoid α] {a b: α}: a ≈ b -> b ≈ b :=
  PSetoid.isper.refl_right

def PSetoid.carrier {α} (S: PSetoid α): Set α := λx: α => S.r x x

def PSetoid.reflSetoid {α} (S: PSetoid α) (refl: ∀x, S.r x x)
  : Setoid α where
  r := S.r
  iseqv := PER.refl_equivalence S.isper refl

def Setoid.toPSetoid {α} (S: Setoid α): PSetoid α where
  r := S.r
  isper := Equivalence.toPER S.iseqv

--TODO: clean this up...
def Relation.onSet {α} (S: Set α) (r: α -> α -> Prop): α -> α -> Prop
  := λa b => a ∈ S ∧ b ∈ S ∧ (r a b)

def Relation.onSet.left {α} {S: Set α} {r} {a b}: onSet S r a b -> S a
  | ⟨H, _, _⟩ => H
def Relation.onSet.right {α} {S: Set α} {r} {a b}: onSet S r a b -> S b
  | ⟨_, H, _⟩ => H
def Relation.onSet.rel {α} {S: Set α} {r} {a b}: onSet S r a b -> r a b
  | ⟨_, _, H⟩ => H

def Relation.onSet_intersect {α} (S R: Set α) (r: α -> α -> Prop)
  : onSet (S ∩ R) r = onSet S r ⊓ onSet R r
  := by
    funext a b
    simp only [onSet, Set.mem_inter_iff, Pi.inf_apply, inf_Prop_eq, eq_iff_iff]
    aesop
def Relation.onSet_sup {α} (S: Set α) (r s: α -> α -> Prop)
  : onSet S r ⊔ onSet S s = onSet S (r ⊔ s)
  := by funext a b; simp only [Pi.sup_apply, onSet, sup_Prop_eq, eq_iff_iff]; aesop
def Relation.onSet_inf {α} (S: Set α) (r s: α -> α -> Prop)
  : onSet S r ⊓ onSet S s = onSet S (r ⊓ s)
  := by funext a b; simp only [Pi.inf_apply, onSet, inf_Prop_eq, eq_iff_iff]; aesop

--TODO: sInf, sSup, etc...

def PER.onSet {α} {r: α -> α -> Prop} (R: PER r) (S: Set α): PER (Relation.onSet S r) where
  symm H := ⟨H.right, H.left, R.symm H.rel⟩
  trans H H' := ⟨H.left, H'.right, R.trans H.rel H'.rel⟩

theorem PER.symmetric {α} {r: α -> α -> Prop} (R: PER r): Symmetric r := λ_ _ => R.symm
theorem PER.transitive {α} {r: α -> α -> Prop} (R: PER r): Transitive r := λ_ _ _ => R.trans

theorem PER.join_eq {α} {r: α -> α -> Prop} (R: PER r): Relation.Join r = r := by
  funext a b; apply propext; constructor
  . intro ⟨_, Hl, Hr⟩; exact R.trans Hl (R.symm Hr)
  . intro H; exact ⟨b, H, R.refl_right H⟩

inductive Relation.PERGen {α} (r: α -> α -> Prop): α -> α -> Prop
  | rel {a b: α}: r a b -> PERGen r a b
  | symm {a b: α}: PERGen r a b -> PERGen r b a
  | trans {a b c: α}: PERGen r a b -> PERGen r b c -> PERGen r a c

theorem PER.PERGen {α} (r: α -> α -> Prop): PER (Relation.PERGen r) where
  symm := Relation.PERGen.symm
  trans := Relation.PERGen.trans

theorem PER.PERGen_self {α} {r: α -> α -> Prop} (R: PER r)
  {a b: α} (H: Relation.PERGen r a b): r a b := by induction H with
  | rel => assumption
  | symm _ I => exact R.symm I
  | trans _ _ I I' => exact R.trans I I'

theorem PER.PERGen_eq_self {α} {r: α -> α -> Prop} (R: PER r):
  Relation.PERGen r = r := funext₂ (λ_ _ => propext ⟨R.PERGen_self, Relation.PERGen.rel⟩)
