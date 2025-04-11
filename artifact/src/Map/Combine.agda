module Map.Combine where

open import Agda.Builtin.Maybe

open import Map.Map
open import Map.Balance
open import Map.Filter
open import Map.Insertion
open import Map.Construction
open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A : Set

union : {{Comparable K}} → Map K A → Map K A → Map K A
union l tip = l
union l (node _ rk ra tip tip) = insertR rk ra l
union (node _ lk la tip tip) r = insert lk la r
union tip r = r
union l@(node _ lk la ll lr) r with split lk r
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

insertWithKeyR : {{Comparable K}} → (f : K → A → A → A) → K → A → Map K A → Map K A
insertWithKeyR _ k' a' tip = singleton k' a'
insertWithKeyR f k' a' (node s k a l r) with compare k' k
insertWithKeyR f k' a' (node s k a l r) | lt = balanceL k a (insertWithKeyR f k' a' l) r
insertWithKeyR f k' a' (node s k a l r) | gt = balanceR k a l (insertWithKeyR f k' a' r)
insertWithKeyR f k' a' (node s k a l r) | eq = node s k (f k a a') l r

unionWithKey : {{Comparable K}} → (K → A → A → A) → Map K A → Map K A → Map K A
unionWithKey f l tip = tip
unionWithKey f l (node rs rk ra tip tip) = insertWithKeyR f rk ra l
unionWithKey f (node ls lk la tip tip) r = insertWithKey f lk la r
unionWithKey f tip r = r
unionWithKey f (node ls lk la ll lr) r with splitLookup lk r
unionWithKey f (node ls lk la ll lr) r | (l' , nothing , r') = link lk la (unionWithKey f ll l') (unionWithKey f lr r')
unionWithKey f (node ls lk la ll lr) r | (l' , just a' , r') = link lk (f lk la a') (unionWithKey f ll l') (unionWithKey f lr r')