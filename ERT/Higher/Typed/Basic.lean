import ERT.Higher.Basic
import ERT.Higher.Typed.Ctx

namespace HERT

open World

-- inductive World.IsMin: World -> World -> World -> Type
--   | ghost_left (w w'): IsMin w ghost w'
--   | ghost_right (w): IsMin ghost comp w
--   | comp: IsMin comp comp comp

inductive Term.IsSort {α}: Term α -> World -> Type
  | prop: Term.IsSort prop ghost
  | type (w): Term.IsSort type w

def Term.IsSort.toGhost {α K w}: @Term.IsSort α K w -> Term.IsSort K ghost
  | prop => prop
  | type _ => type ghost

inductive Term.PiType {α}: World -> Term α -> Term α -> Term α -> World -> Type
  | pi (w): PiType comp type type type w
  | inter (w): PiType ghost type type type w
  | checked: PiType comp type prop prop ghost
  | forall_: PiType ghost type prop prop ghost
  | assume (w): PiType ghost prop type type w
  | implies: PiType ghost prop prop prop ghost

def Term.PiType.toGhost {α w} {KA KB KC: Term α} {rw}
  : Term.PiType w KA KB KC rw -> Term.PiType w KA KB KC ghost
  | pi _ => pi ghost
  | inter _ => inter ghost
  | checked => checked
  | forall_ => forall_
  | assume _ => assume ghost
  | implies => implies

-- inductive Term.SigmaType {α}: World -> Term α -> Term α -> Term α -> World -> Type
--   | sigma (w): SigmaType comp type type type w
--   | union (w): SigmaType ghost type type type w
--   | set (w): SigmaType comp type prop type w
--   | exists_: SigmaType ghost type prop prop ghost
--   | valid (w): SigmaType ghost prop type type w
--   | and: SigmaType ghost prop prop prop ghost

-- def Term.SigmaType.toGhost {α w} {KA KB KC: Term α} {rw}
--   : Term.SigmaType w KA KB KC rw -> Term.SigmaType w KA KB KC ghost
--   | sigma _ => sigma ghost
--   | union _ => union ghost
--   | set _ => set ghost
--   | exists_ => exists_
--   | valid _ => valid ghost
--   | and => and

inductive Term.HasType {α}: List (Var α) -> Term α -> Term α -> World -> Type
  -- Variables
  | var {Γ n A KA w}: HasVar Γ n A w
    -> HasType Γ A KA w -> IsSort KA w
    -> HasType Γ (var n) A w

  -- Term/type formers
  -- NOTE: no need to shift down kind variables in
  -- The whole IsSort KB w vs IsSort KB rw hack is to cleanly disallow pi (x: comp A) -> φ;
  -- propositions should only depend on ghosts!
  | pi
    : HasType Γ A KA w
    -> IsSort KA w
    -> HasType (Var.mk A w :: Γ) B KB rw
    -> IsSort KB w -- NOTE: IsSort KB rw is implied here!
    -> HasType Γ (pi w A B) KB rw
  -- | sigma {Γ w A KA wA B KB wB KC wC}
  --   : HasType Γ A KA wA
  --   -> HasType (Var.mk A w :: Γ) B KB wB
  --   -> SigmaType w KA KB KC wC
  --   -> HasType Γ (sigma w A B) KB wC
  -- | coprod {Γ K A wA B wB wC}
  --   : HasType Γ A K wA -> HasType Γ B K wB -> HasType Γ (coprod A B) K wC

  -- Base types
  | unit (Γ w): HasType Γ unit type w
  | nat (Γ w): HasType Γ nat type w
  | prop (Γ): HasType Γ prop type ghost

  -- Base propositions
  | top (Γ): HasType Γ top prop ghost
  | bot (Γ): HasType Γ bot prop ghost
  | eq: HasType Γ A type wA
    -> HasType Γ a A wa
    -> HasType Γ b A wb
    -> HasType Γ (eq a b) prop ghost

  -- Term/proof formers
  | lam: HasType Γ A KA w -> IsSort KA w
    -> HasType (Var.mk A w :: Γ) t B rw
    -> HasType (Var.mk A w :: Γ) B KB w -- NOTE: HasType (Var.mk A w :: Γ) B KB rw is implied here!
    -> HasType Γ (lam w A t) (pi w A B) rw
  | app: HasType Γ s (pi pw A B) rw
    -> HasType Γ t A aw
    -> B.subst t.subst0 = B'
    -- -> IsMin pw rw aw
    -> HasType Γ (app s t) B' rw
  --TODO: let1
  --TODO: let2

def Term.HasType.toGhost {α Γ} {a A: Term α} {w}
  : Term.HasType Γ a A w -> Term.HasType Γ a A ghost
  | var Hv HA HK => var Hv.toGhost HA.toGhost HK.toGhost
  | pi HA HKA HB HKB => pi HA HKA HB.toGhost HKB
  | unit Γ _ => unit Γ ghost
  | nat Γ _ => nat Γ ghost
  | prop Γ => prop Γ
  | top Γ => top Γ
  | bot Γ => bot Γ
  | eq HA Ha Hb => eq HA Ha Hb
  | lam HA HKA Ht HB => lam HA HKA Ht.toGhost HB
  | app Hs Ht E => app Hs.toGhost Ht E -- (IsMin.ghost_left _ _)

inductive Term.IsKind {α}: List (Var α) -> Term α -> World -> Type
  | meta (Γ w): IsKind Γ type w
  | sort {Γ A K w}: IsSort K w -> HasType Γ A K w -> IsKind Γ A w

abbrev Term.IsKind.type {α Γ A w} (H: @HasType α Γ A type w): IsKind Γ A w :=
  IsKind.sort (IsSort.type _) H

-- abbrev Term.IsKind.prop {α Γ A w} (H: @HasType α Γ A prop w): IsKind Γ A w :=
--   IsKind.sort IsSort.prop H

def Term.IsKind.kindSort {α Γ K w w'}: @IsKind α Γ K w -> IsSort K w' -> IsSort K w
  | _, IsSort.type _ => IsSort.type _
  | IsKind.sort _ H, IsSort.prop =>
    have H': w = ghost := by cases H; rfl;
    H' ▸ IsSort.prop

def Term.IsSort.toKind {α K w} (Γ): @IsSort α K w -> Term.IsKind Γ K w
  | type _ => IsKind.meta _ _
  | prop => IsKind.sort (IsSort.type _) (HasType.prop _)

-- def Term.HasType.regular {α Γ} {a A: Term α} {w}
--   : Term.HasType Γ a A w -> Term.IsKind Γ A w
--   | var _ HA HK => IsKind.sort HK HA
--   | pi _ _ HB HKB => (IsKind.kindSort HB.regular HKB).toKind _
--   | unit _ _ | nat _ _ | prop _ => IsKind.meta _ _
--   | top _ | bot _ | eq _ _ _ => IsKind.type (HasType.prop _)
--   | lam HA HKA Ht HB =>
--     have Hb' := Ht.regular;
--     match Hb' with
--     | IsKind.meta _ _ => by cases HB
--     | IsKind.sort Hb' Hb'' => IsKind.sort sorry (pi sorry sorry sorry)
--   | app _ _ _ => sorry
