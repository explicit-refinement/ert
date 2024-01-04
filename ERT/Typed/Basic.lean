import ERT.Untyped.Basic

structure Var (α) where
  kind: Kind
  ty: Term α

structure Var.le {α} (a b: Var α): Prop where
  kind: a.kind.le b.kind
  ty: a.ty = b.ty

inductive Downgrade {α}: List (Var α) -> List (Var α) -> Type
  | nil: Downgrade [] []
  | cons: ∀ {x y xs ys}, x.le y -> Downgrade xs ys -> Downgrade (x :: xs) (y :: ys)

inductive HasVar {α}: List (Var α) -> ℕ -> Term α -> Type where
  | head: ∀ {xs x}, x.kind.solid -> HasVar (x :: xs) 0 x.ty
  | tail: ∀ {xs x y n}, HasVar xs n x -> HasVar (y :: xs) (n + 1) x

inductive Term.HasKind {α}: Term α -> Kind -> Prop where
  | prop: Term.HasKind Term.prop Kind.prop
  | type w: Term.HasKind Term.type (Kind.type w)

def Term.IsKind {α}: Term α -> Prop := λt => ∃k, Term.HasKind t k

inductive Term.HasType {α}: List (Var α) -> Term α -> Term α -> Type
  -- Variables
  | var {Γ n A}: HasVar Γ n A -> HasType Γ (var n) A

  -- Type/proposition formers
  | pi {Γ k A KA B KB}:
    HasType Γ A KA -> HasKind KA k
    -> HasType (⟨k, A⟩ :: Γ) B KB
    -> HasType Γ (Term.pi k A B) KB
  | sigma {Γ k A KA B KB KC}:
    HasType Γ A KA -> Term.HasKind KA k
    -> HasType (⟨k, A⟩ :: Γ) B KB
    -> Term.IsKind KC -> HasType Γ (Term.pi k A B) KC
  | coprod {Γ A B K}
    : HasType Γ A K -> HasType Γ B K -> HasType Γ (Term.coprod A B) Term.type

  -- Base types
  | unit: HasType Γ unit type
  | nat: HasType Γ nat type
  | prop: HasType Γ prop type

  -- Base propositions
  | top: HasType Γ top prop
  | bot: HasType Γ bot prop
  | eq {Γ A a b}: HasType Γ A type -> HasType Γ a A -> HasType Γ b A -> HasType Γ (eq a b) prop

  -- Term/proof formers
  -- | let1 {Γ k A KA B KB a e}
  --   : HasType Γ A KA -> Term.HasKind KA k
  --   -> HasType Γ B KB -> Term.IsKind KB
  --   -> HasType Γ a A -> HasType (⟨k, a⟩ :: Γ) e B
  --   -> HasType Γ (let1 a e) B
  | lam {Γ k A KA t B KB}: HasType Γ A KA -> Term.HasKind KA k
    -> HasType Γ B KB
    -> HasType (⟨k, a⟩ :: Γ) t B -> HasType Γ (lam k A t) (pi k A B)
  --TODO: downgrade here?
  | app {Γ k A B s t}: HasType Γ s (pi k A B) -> HasType Γ t A -> HasType Γ (app s t) B
