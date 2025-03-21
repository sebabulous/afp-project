module Map.DeletionUpdate where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe

open import Map.Construction
open import Map.Query
open import Map.Balance
open import Map.Map

----------------------------------
-- Deletion/ Update
----------------------------------

delete : {K V : Set} → {{Comparable K}} → K → Map K V → Map K V
delete _ tip = tip
delete k (node _ k' v l r) with compare k k'
...                       | lt = balanceR k' v (delete k l) r
...                       | gt = balanceL k' v l (delete k r)
...                       | eq = glue l r

adjustWithKey : {K V : Set} → {{Comparable K}} → (K → V → V) → K → Map K V → Map K V
adjustWithKey _ _ tip = tip
adjustWithKey f k (node s k' v l r) with compare k k'
...                                 | lt = node s k' v (adjustWithKey f k l) r
...                                 | gt = node s k' v l (adjustWithKey f k r)
...                                 | eq = node s k' (f k' v) l r

adjust : {K V : Set} → {{Comparable K}} → (V → V) → K → Map K V → Map K V
adjust f = adjustWithKey (λ _ v → f v)

updateWithKey : {K V : Set} → {{Comparable K}} → (K → V → Maybe V) → K → Map K V → Map K V
updateWithKey _ _ tip = tip
updateWithKey f k (node s k' v l r) with compare k k'
...                                 | lt = balanceR k' v (updateWithKey f k l) r
...                                 | gt = balanceL k' v l (updateWithKey f k r)
...                                 | eq with f k' v
...                                      | just v' = node s k' v' l r
...                                      | nothing = glue l r

update : {K V : Set} → {{Comparable K}} → (V → Maybe V) → K → Map K V → Map K V
update f = updateWithKey (λ _ v → f v)

updateLookupWithKey' : {K V : Set} → {{Comparable K}} → (K → V → Maybe V) → K → Map K V → StrictPair (Maybe V) (Map K V)
updateLookupWithKey' _ _ tip = nothing :*: tip
updateLookupWithKey' f k (node s k' v l r) with compare k k'
...                                        | lt with updateLookupWithKey' f k l
...                                             | found :*: l' = found :*: balanceR k' v l' r
updateLookupWithKey' f k (node s k' v l r) | gt with updateLookupWithKey' f k r
...                                             | found :*: r' = found :*: balanceL k' v l r'
updateLookupWithKey' f k (node s k' v l r) | eq with f k' v
...                                             | just v' = just v' :*: node s k' v' l r
...                                             | nothing = just v :*: glue l r
updateLookupWithKey : {K V : Set} → {{Comparable K}} → (K → V → Maybe V) → K → Map K V → Pair (Maybe V) (Map K V)
updateLookupWithKey f k m = toPair (updateLookupWithKey' f k m)

alter : {K V : Set} → {{Comparable K}} → (Maybe V → Maybe V) → K → Map K V → Map K V
alter f k tip with f nothing
...           | nothing = tip
...           | just v = singleton k v
alter f k (node s k' v l r) with compare k k'
...                         | lt = balance k' v (alter f k l) r
...                         | gt = balance k' v l (alter f k r)
...                         | eq with f (just v)
...                              | just v' = node s k' v' l r
...                              | nothing = glue l r

-- atKeyImpl : {K V : Set} → {{Functor F}} → {{Comparable K}} → AreWeStrict → K → (Maybe V → F (Maybe V)) → Map K V → F (Map K V)
-- atKeyImpl strict k f m with wordSize < 61 && size m >= alterFCutoff
-- ...                    | true = alterFFallback strict k f m
-- atKeyImpl strict k f m with lookupTract k m
-- ...                    | TraceResult mv q 

-- alterF : {K V : Set} → {{Functor F}} → {{Comparable K}} → (Maybe V → F (Maybe V)) → K → Map K V → F (Map K V)
-- alterF f k m = atKeyImpl Lazy k f m

