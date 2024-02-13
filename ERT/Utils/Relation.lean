import Mathlib.Logic.Relation

def Relation.SymmGen (α : Type u) (r : α → α → Prop) : α → α → Prop := λa b => r a b ∨ r b a

def Relation.symmGen_eq_self {α} {r : α → α → Prop} (Hr: Symmetric r): Relation.SymmGen α r = r
  := funext₂ (λ_ _ => propext ⟨λH => H.elim id (λp => Hr p), Or.inl⟩)
