module Tests.Valid where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

open import Map.Query
open import Map.Balance
open import Map.Map

private variable
  K A : Set

balanced : Map K A → Bool
balanced tip = true
balanced (node _ _ _ l r) =  (check1 || check2) && balanced l && balanced r
  where
    check1 : Bool
    check1 with compare (size l + size r) 1
    ...    | gt = false
    ...    | _ = true

    check2 : Bool
    check2 with (compare (size l) (delta * size r) , compare (size r) (delta * size l))
    ...    | (gt , _) = false
    ...    | (_ , gt) = false
    ...    | (_ , _) = true

ordered : {{Comparable K}} → Map K A → Bool
ordered t = bounded (λ _ → true) (λ _ → true) t
  where
    bounded : ∀{A} → {{Comparable K}} → (K → Bool) → (K → Bool) → Map K A → Bool
    bounded _ _ tip = true
    bounded lo hi (node _ kx _ l r) = (lo kx) && hi kx && bounded lo (ltkx kx) l && bounded (gtkx kx) hi r
      where
        ltkx : {{Comparable K}} → K → K → Bool
        ltkx kx' k with compare k kx'
        ...    | lt = true
        ...    | _ = false

        gtkx : {{Comparable K}} → K → K → Bool
        gtkx kx' k with compare k kx'
        ...    | gt = true
        ...    | _ = false

slowSize : Map K A → Maybe Nat
slowSize tip = just 0
slowSize (node sz _ _ l r) with (slowSize l , slowSize r)
...                        | (nothing , _) = nothing
...                        | (_ , nothing) = nothing
...                        | (just ls , just rs) with compare sz (ls + rs + 1)
...                                              | eq = just sz
...                                              | _ = nothing

validsize : Map K A → Bool
validsize t with slowSize t
...         | nothing = false
...         | just _ = true

valid : {{Comparable K}} → Map K A → Bool
valid t = balanced t && ordered t && validsize t