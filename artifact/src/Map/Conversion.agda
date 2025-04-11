module Map.Conversion where

open import Agda.Builtin.Nat

open import Map.Map
open import Map.Folds

private variable
  K V : Set
  n : Nat

elems : Map K V n → Vec V n
-- elems = foldr _∷_ []
elems tip = []
elems (node k a l r) = elems l ++ (a ∷ elems r)

-- foldr : {V K A : Set} → (A → V → V) → V → Map K A n → V
-- foldr f v tip = v
-- foldr f v (node k a l r) = foldr f (f a (foldr f v r)) l

toVec : Map K V n → Vec (Pair K V) n
toVec tip = []
toVec (node k a l r) = toVec l ++ ((k , a) ∷ toVec r)