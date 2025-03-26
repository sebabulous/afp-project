module Map.Indexed where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

open import Map.Query
open import Map.Map
open import Map.Balance

private variable
  K A : Set
  m n : Nat

-- data ReducedMap K A : (m : Nat) → (n : Nat) → Set where
--   reducedAll : Map K A zero → ReducedMap K A zero n
--   reducedSome : (m : Nat) → (n : Nat) → Map K A m → ReducedMap K A m n
-- data ReducedMap K A : (m : Nat) → (n : Nat) → Set where
--   reducedAll : Map K A zero → ReducedMap K A 

lookupIndex : {{Comparable K}} → K → Map K A n → Maybe Nat
lookupIndex = go 0
  where
    go : {{Comparable K}} → Nat → K → Map K A n → Maybe Nat
    go _ _ tip = nothing
    go idx k (node _ kx _ l r) with compare k kx
    ...                                 | lt = go idx k l
    ...                                 | gt = go (idx + size l + 1) k r
    ...                                 | eq = just (idx + size l)

-- findIndex (partial)

-- elemAt (partial)

-- updateAt (partial)

-- deleteAt (partial)

take i0 m0 with compare i0 (size m0)
...      | gt = m0
...      | eq = m0
...      | lt = go i0 m0
  where
    go : {{Comparable K}} → Nat → Map K A → Map K A
    go _ tip = tip
    go i (node _ kx x l r) with compare i 0
    ...                    | lt = tip
    ...                    | eq = tip
    ...                    | gt with compare i (size l)
    ...                         | lt = go i l
    ...                         | gt = link kx x l (go (i - (size l) - 1) r)
    ...                         | eq = l

drop : {{Comparable K}} → Nat → Map K A → Map K A
drop i0 m0 with compare i0 (size m0)
...        | gt = tip
...        | eq = tip
...        | lt = go i0 m0
  where
    go : {{Comparable K}} → Nat → Map K A → Map K A
    go _ tip = tip
    go i m@(node _ kx x l r) with compare i 0
    ...                    | lt = m
    ...                    | eq = m
    ...                    | gt with compare i (size l)
    ...                         | lt = link kx x (go i l) r
    ...                         | gt = go (i - (size l) - 1) r
    ...                         | eq = insertMin kx x r

splitAt : {{Comparable K}} → Nat → Map K A → Pair (Map K A) (Map K A)
splitAt i0 m0 with compare i0 (size m0)
...           | gt = (m0 , tip)
...           | eq = (m0 , tip)
...           | lt = toPair (go i0 m0)
  where
    go : {{Comparable K}} → Nat → Map K A → StrictPair (Map K A) (Map K A)
    go _ tip = tip :*: tip
    go i m@(node _ kx x l r) with compare i 0
    ...                      | lt = tip :*: m
    ...                      | eq = tip :*: m
    ...                      | gt with compare i (size l)
    ...                           | lt = let mm = go i l in (fst mm) :*: link kx x (snd mm) r
    ...                           | gt = let mm = go (i - (size l) - 1) r in link kx x l (fst mm) :*: (snd mm)
    ...                           | eq = l :*: insertMin kx x r 