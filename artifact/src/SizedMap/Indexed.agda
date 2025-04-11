module SizedMap.Indexed where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

open import SizedMap.Query
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Map
open import SizedMap.Balance

private variable
  K A : Set
  m n : Nat

lookupIndex : {{Comparable K}} → K → Map K A n → Maybe Nat
lookupIndex = go 0
  where
    go : {{Comparable K}} → Nat → K → Map K A n → Maybe Nat
    go _ _ tip = nothing
    go idx k (node kx _ l r) with compare k kx
    ...                                 | lt = go idx k l
    ...                                 | gt = go (idx + size l + 1) k r
    ...                                 | eq = just (idx + size l)

take : {{Comparable K}} → (m : Nat) → Map K A n → Σ Nat (Map K A)
take i0 m0 with compare i0 (size m0)
take i0 m0 | gt = (size m0 , m0)
take i0 m0 | eq = (size m0 , m0)
take i0 m0 | lt = go i0 m0
  where
    go : {{Comparable K}} → Nat → Map K A n → Σ Nat (Map K A)
    go _ tip = (zero , tip)
    go i (node kx x l r) with compare i 0
    go i (node kx x l r) | lt = (zero , tip)
    go i (node kx x l r) | eq = (zero , tip)
    go i (node kx x l r) | gt with compare i (size l)
    go i (node kx x l r) | gt | lt = go i l
    go i (node kx x l r) | gt | eq = (size l , l)
    go i (node kx x l r) | gt | gt with go (i - (size l) - 1) r
    go i (node kx x l r) | gt | gt | (s , r') = (suc (size l + s) , link kx x l r')

drop : {{Comparable K}} → Nat → Map K A n → Σ Nat (Map K A)
drop i0 m0 with compare i0 (size m0)
drop i0 m0 | gt = (zero , tip)
drop i0 m0 | eq = (zero , tip)
drop i0 m0 | lt = go i0 m0
  where
    go : {{Comparable K}} → Nat → Map K A n → Σ Nat (Map K A)
    go _ tip = (zero , tip)
    go i m@(node kx x l r) with compare i 0
    go i m@(node kx x l r) | lt = (size m , m)
    go i m@(node kx x l r) | eq = (size m , m)
    go i m@(node kx x l r) | gt with compare i (size l)
    go i m@(node kx x l r) | gt | lt with go i l
    go i m@(node kx x l r) | gt | lt | (s , l') = (suc (size l' + size r) , link kx x l' r)
    go i m@(node kx x l r) | gt | gt = go (i - (size l) - 1) r
    go i m@(node kx x l r) | gt | eq = ((size r + 1) , insertMin kx x r)

splitAt : {{Comparable K}} → Nat → Map K A n → Σ (Pair Nat Nat) (λ (m₁ , m₂) → Pair (Map K A m₁) (Map K A m₂))
splitAt i0 m0 with compare i0 (size m0)
splitAt i0 m0 | gt = ((size m0 , zero) , (m0 , tip))
splitAt i0 m0 | eq = ((size m0 , zero) , (m0 , tip))
splitAt i0 m0 | lt = (go i0 m0)
  where
    go : {{Comparable K}} → Nat → Map K A n → Σ (Pair Nat Nat) (λ (m₁ , m₂) → Pair (Map K A m₁) (Map K A m₂))
    go _ tip = (zero , zero) , (tip , tip)
    go i m@(node kx x l r) with compare i 0
    go i m@(node kx x l r) | lt = (zero , size m) , (tip , m)
    go i m@(node kx x l r) | eq = (zero , size m) , (tip , m)
    go i m@(node kx x l r) | gt with compare i (size l)
    go i m@(node kx x l r) | gt | lt with go i l
    go i m@(node kx x l r) | gt | lt | ((s₁ , s₂) , (mm₁ , mm₂)) = (s₁ , suc (s₂ + size r)) , (mm₁ , link kx x mm₂ r)
    go i m@(node kx x l r) | gt | gt with go (i - (size l) - 1) r
    go i m@(node kx x l r) | gt | gt | ((s₁ , s₂) , (mm₁ , mm₂)) = (suc (size l + s₁) , s₂) , (link kx x l mm₁ , mm₂)
    go i m@(node kx x l r) | gt | eq = (size l , suc (size r)) , (l , insertMin kx x r)