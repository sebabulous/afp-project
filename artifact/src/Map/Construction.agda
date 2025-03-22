module Map.Construction where

open import Agda.Builtin.List

open import Map.Map
open import Map.Insertion

empty : {K V : Set} -> Map K V
empty = tip

singleton : {K V : Set} -> K -> V -> Map K V
singleton k v = node 1 k v tip tip

-- does the set collection not exist in agda?
-- fromSet
-- fromArgSet

foldlList : {E R : Set} → (R → E → R) → R → List E → R
foldlList _ v []       = v
foldlList f v (x ∷ xs) = foldlList f (f v x) xs

fromList : {K V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 
fromList = foldlList (λ m (k , v) → insert k v m) tip

fromListWith : {K V : Set} → {{Comparable K}} → (V → V → V) → List (Pair K V) → Map K V
fromListWith f = foldlList (λ m (k , v) → insertWith f k v m) tip

fromListWithKey : {K V : Set} → {{Comparable K}} → (K → V → V → V) → List (Pair K V) → Map K V
fromListWithKey f = foldlList (λ m (k , v) → insertWithKey f k v m) tip

fromAscList : {K V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 
fromAscListWith : {K V : Set} → {{Comparable K}} → (V → V → V) → List (Pair K V) → Map K V
fromAscListWithKey : {K V : Set} → {{Comparable K}} → (K → V → V → V) → List (Pair K V) → Map K V
fromDistinctAscList : {K V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 

fromAscList = fromAscListWithKey (λ _ v _ → v)

fromAscListWith f = fromAscListWithKey (λ _ v₁ v₂ → f v₁ v₂)

fromAscListWithKey = {!  !}

fromDistinctAscList = {!  !}


fromDescList : {K V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 
fromDescListWith : {K V : Set} → {{Comparable K}} → (V → V → V) → List (Pair K V) → Map K V
fromDescListWithKey : {K V : Set} → {{Comparable K}} → (K → V → V → V) → List (Pair K V) → Map K V
fromDistinctDescList : {K V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 

fromDescList = fromDescListWithKey (λ _ v _ → v)

fromDescListWith f = fromDescListWithKey (λ _ v₁ v₂ → f v₁ v₂)

fromDescListWithKey = {!  !}

fromDistinctDescList = {!  !}