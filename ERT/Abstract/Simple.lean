import ERT.Abstract.Basic

namespace Abstract

class SimplyTyped.{w} (α: Type u) (τ: outParam (Type v)) extends Syntax α where
  wellTyped: (a: α)
    -> (Fin (arity a) -> τ)
    -> ((i: Fin (arity a)) -> (Fin (binding a i)) -> τ)
    -> τ
    -> Sort w

structure Ctx (τ) where
  len: ℕ
  types: Fin len -> τ
