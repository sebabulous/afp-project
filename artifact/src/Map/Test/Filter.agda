module Map.Test.Filter where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Map.Test.Cases
open import Map.Test.Balance
open import Helpers.Pair
open import Helpers.Comparable
open import Map.Filter
open import Map.Map

private variable
  K A B : Set
  k k' : K
  a a' : A

data either A B : Set where
  left : A → either A B
  right : B → either A B



-- Finishing this proof is straightforward when all balancing functions have been proven
filterFilters : {{_ : Comparable K}} → {f : K → A → Bool} → {m : Map K A} → f k a ≡ true → (k , a) ∈ m → (k , a) ∈ filterWithKey f m
filterFilters {f = f} {m = node s k a l r} fka≡true here with f k a
filterFilters {f = f} {m = node s k a l r} fka≡true here | true = linkRetainsElementsHere {_} {_} {_} {_} {filterWithKey f l} {filterWithKey f r}
filterFilters {f = f} {m = node s k a l r} fka≡true (thereL prf) with f k a
filterFilters {f = f} {m = node s k a l r} fka≡true (thereL prf) | true = linkRetainsElementsL {_} {_} {_} {k} {_} {a} {filterWithKey f l} {filterWithKey f r} (filterFilters {f = f} fka≡true prf)
filterFilters {f = f} {m = node s k a l r} fka≡true (thereL prf) | false = {!   !}
filterFilters {f = f} {m = node s k a l r} fka≡true (thereR prf) with f k a
filterFilters {f = f} {m = node s k a l r} fka≡true (thereR prf) | true = {!   !}
filterFilters {f = f} {m = node s k a l r} fka≡true (thereR prf) | false = {!   !}
