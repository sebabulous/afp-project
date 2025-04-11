module SizedMap.Test.Valid where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

open import SizedMap.Query
open import SizedMap.Balance
open import SizedMap.Map
open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A : Set
  m n : Nat

balanced : Map K A n → Bool
balanced tip = true
balanced (node _ _ l r) with (compare (size l + size r) 1 , (compare (size l) (delta * size r) , compare (size r) (delta * size l)))
balanced (node _ _ l r) | (gt , (gt , _)) = false
balanced (node _ _ l r) | (gt , (_ , gt)) = false
balanced (node _ _ l r) | _ = balanced l && balanced r

ordered : {{Comparable K}} → Map K A n → Bool
ordered t = bounded (λ _ → true) (λ _ → true) t
  where
    bounded : ∀{A} → {{Comparable K}} → (K → Bool) → (K → Bool) → Map K A n → Bool
    bounded _ _ tip = true
    bounded lo hi (node kx _ l r) = (lo kx) && hi kx && bounded lo (ltkx kx) l && bounded (gtkx kx) hi r
      where
        ltkx : {{Comparable K}} → K → K → Bool
        ltkx kx' k with compare k kx'
        ...    | lt = true
        ...    | _ = false

        gtkx : {{Comparable K}} → K → K → Bool
        gtkx kx' k with compare k kx'
        ...    | gt = true
        ...    | _ = false

valid : {{Comparable K}} → Map K A n → Bool
valid t = balanced t && ordered t