module SizedMap.DeletionUpdate where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe

open import SizedMap.Construction
open import SizedMap.Query
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Balance
open import SizedMap.Map


private variable
  K A : Set
  m n : Nat

delete : {{Comparable K}} → K → Map K A (suc n) → Maybe (Map K A n)
delete k (node k' v tip tip) with compare k k'
...                            | eq = just tip
...                            | _ = nothing
delete k (node k' v l r) with (l , r , compare k k')
...                        | (tip , _ , lt) = nothing
...                        | (node _ _ _ _ , _ , lt) with delete k l
...                            | nothing = nothing
...                            | just l' = just (balanceR k' v l' r)
delete k (node k' v l r) | (_ , tip , gt) = nothing
delete k (node k' v l r) | (_ , node _ _ _ _ , gt) with delete k r
...                                                    | nothing = nothing
...                                                    | just r' = just (balanceL k' v l r')
delete k (node k' v l r) | (_ , _ , eq) = just (glue l r)

adjustWithKey : {{Comparable K}} → (K → A → A) → K → Map K A n → Map K A n
adjustWithKey _ _ tip = tip
adjustWithKey f k (node k' v l r) with compare k k'
...                                 | lt = node k' v (adjustWithKey f k l) r
...                                 | gt = node k' v l (adjustWithKey f k r)
...                                 | eq = node k' (f k' v) l r

adjust : {{Comparable K}} → (A → A) → K → Map K A n → Map K A n
adjust f = adjustWithKey (λ _ v → f v)

updateWithKey : {{Comparable K}} → (K → A → Maybe A) → K → Map K A n → MapMod K A n
updateWithKey _ _ tip = modId tip
updateWithKey f k (node k' v l r) with compare k k'
...                                 | lt with updateWithKey f k l
...                                      | modDelete l' = modDelete (balanceR k' v l' r)
...                                      | modInsert l' = modInsert (balanceR k' v l' r)
...                                      | modId l' = modId (balanceR k' v l' r)
updateWithKey f k (node k' v l r) | gt with updateWithKey f k r
...                                      | modDelete r' = modDelete (balanceL k' v l r')
...                                      | modInsert r' = modInsert (balanceL k' v l r')
...                                      | modId r' = modId (balanceL k' v l r')
updateWithKey f k (node k' v l r) | eq with f k' v
...                                      | just v' = modId (node k' v' l r)
...                                      | nothing = modDelete (glue l r)

update : {{Comparable K}} → (A → Maybe A) → K → Map K A n → MapMod K A n
update f = updateWithKey (λ _ v → f v)

updateLookupWithKey' : {{Comparable K}} → (K → A → Maybe A) → K → Map K A n → StrictPair (Maybe A) (MapMod K A n)
updateLookupWithKey' _ _ tip = nothing :*: modId tip
updateLookupWithKey' f k (node k' v l r) with compare k k'
...                                        | lt with updateLookupWithKey' f k l
...                                             | found :*: modInsert l' = found :*: modInsert (balanceR k' v l' r)
...                                             | found :*: modId l' = found :*: modId (balanceR k' v l' r)
...                                             | found :*: modDelete l' = found :*: modDelete (balanceR k' v l' r)
updateLookupWithKey' f k (node k' v l r) | gt with updateLookupWithKey' f k r
...                                             | found :*: modInsert r' = found :*: modInsert (balanceL k' v l r')
...                                             | found :*: modId r' = found :*: modId (balanceL k' v l r')
...                                             | found :*: modDelete r' = found :*: modDelete (balanceL k' v l r')
updateLookupWithKey' f k (node k' v l r) | eq with f k' v
...                                             | just v' = just v' :*: modId (node k' v' l r)
...                                             | nothing = just v :*: modDelete (glue l r)
updateLookupWithKey : {{Comparable K}} → (K → A → Maybe A) → K → Map K A n → Pair (Maybe A) (MapMod K A n)
updateLookupWithKey f k m = toPair (updateLookupWithKey' f k m)

alter : {{Comparable K}} → (Maybe A → Maybe A) → K → Map K A n → MapMod K A n
alter f k tip with f nothing
...           | nothing = modId tip
...           | just v = modInsert (singleton k v)
alter f k (node k' v l r) with compare k k'
...                         | lt with alter f k l
...                              | modId l' = modId (balance k' v l' r)
...                              | modDelete l' = modDelete (balance k' v l' r)
...                              | modInsert l' = modInsert (balance k' v l' r)
alter f k (node k' v l r) | gt with alter f k r
...                              | modId r' = modId (balance k' v l r')
...                              | modDelete r' = modDelete (balance k' v l r')
...                              | modInsert r' = modInsert (balance k' v l r')
alter f k (node k' v l r) | eq with f (just v)
...                              | just v' = modId (node k' v' l r)
...                              | nothing = modDelete (glue l r)