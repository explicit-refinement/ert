import Mathlib.Logic.Relation

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
