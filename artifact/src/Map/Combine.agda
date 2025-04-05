module Map.Combine where

open import Agda.Builtin.Maybe

open import Map.Map
open import Map.Balance
open import Map.Filter
open import Map.Insertion

private variable
  K A : Set

union : {{Comparable K}} → Map K A → Map K A → Map K A
union l tip = l
union l (node _ rk ra tip tip) = insertR rk ra l
union (node _ lk la tip tip) r = insert lk la r
union tip r = r
union l@(node _ lk la ll lr) r with split lk l
... | (l2 , r2) = link lk la (union ll l2) (union lr r2)

unionWith : {{Comparable K}} → (A → A → A) → Map K A → Map K A → Map K A
unionWith _ l tip = l
unionWith f l (node _ rk ra tip tip) = insertWithR f rk ra l
unionWith f (node _ lk la tip tip) r = insertWith f lk la r
unionWith _ tip r = r
unionWith f (node _ lk la ll lr) r with splitLookup lk r
unionWith f (node _ lk la ll lr) r | (l2 , mb , r2) with mb
unionWith f (node _ lk la ll lr) r | (l2 , mb , r2) | nothing = link lk la (unionWith f ll l2) (unionWith f lr r2)
unionWith f (node _ lk la ll lr) r | (l2 , mb , r2) | just x2 = link lk (f la x2) (unionWith f ll l2) (unionWith f lr r2)