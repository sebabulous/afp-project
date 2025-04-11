module Helpers.Comparable where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Helpers.Provers

data Ord : Set where
  eq : Ord
  lt : Ord
  gt : Ord

record Comparable (A : Set) : Set where
  field
    compare : A → A → Ord
    compare-reflexive : ∀ k → compare k k ≡ eq
    compare-reflexive-2 : ∀{k k'} → compare k k' ≡ eq → k ≡ k'

open Comparable {{...}} public

instance
  NatCmp : Comparable Nat
  compare {{ NatCmp }} zero zero = eq
  compare {{ NatCmp }} zero (suc _) = lt
  compare {{ NatCmp }} (suc _) zero = gt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

  compare-reflexive {{ NatCmp }} zero = refl
  compare-reflexive {{ NatCmp }} (suc n) = compare-reflexive n

  compare-reflexive-2 ⦃ NatCmp ⦄ {zero} {zero} p = refl
  compare-reflexive-2 ⦃ NatCmp ⦄ {suc k} {suc k'} p = cong suc (compare-reflexive-2 {k = k} {k' = k'} p)