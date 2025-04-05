module Test.Insertion where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Map.Map
open import Map.Insertion

private variable
  K A : Set

data _∈_ (x : Pair K A) : Map K A → Set where
  here : ∀{s l r} → let record {fst = k ; snd = a} = x in x ∈ node s k a l r
  thereL : ∀{s k a l r} → x ∈ l → x ∈ node s k a l r
  thereR : ∀{s k a l r} → x ∈ r → x ∈ node s k a l r

insertInserts : {{k : Comparable K}} → {k : K} → {a : A} → {m : Map K A} → (k , a) ∈ insert k a m
insertInserts {m = tip} = here
insertInserts {k = k} {a} {m = node s k' a' l r} with compare k k'
... | eq = here
... | lt = thereL (insertInserts {k = k} {a = a} {l})
... | gt = thereR (insertInserts {k = k} {a = a} {r})

-- insertWithModifies : {{k : Comparable K}} → {f : A → A → A} → {k : K} → {a : A} → {a' : A} → {m : Map K A} → (k , a') ∈ m → (k , f a a') ∈ insertWith f k a m
-- insertWithModifies {f = f} {k = k} {a = a} {a' = a'} {m = node s k a' l r} here with compare k k
-- ... | eq = here
-- ... | lt = {!   !}
-- ... | gt = {!   !}
-- insertWithModifies {f = f} {k = k} {a = a} {m = node s k' a' l r} (thereL prf) with compare k k'
-- ... | eq = {!   !}
-- ... | lt = thereL (insertWithModifies {f = f} {k = k} {a = a} {m = l} prf)
-- ... | gt = {!   !}
-- insertWithModifies {f = f} {k = k} {a = a} {m = node s k' a' l r} (thereR prf) with compare k k'
-- ... | eq = {!   !}
-- ... | lt = {!   !}
-- ... | gt = thereR (insertWithModifies {f = f} {k = k} {a = a} {m = r} prf)

-- insertWithInserts : {{_ : Comparable K}} → {f : A → A → A} → {k : K} → {a : A} → {m : Map K A} → _∉k_ {_} {_} {a} k m → (k , a) ∈ insertWith f k a m
-- insertWithInserts kNotHere = here
-- -- insertWithInserts {K} {A} {f} {k} {a} {m = node s k' a' l r} (kNotThereL x₁ y) = insertWithInserts {f = f} {k = k} {a = a} {!   !}
-- insertWithInserts {K} {A} {f} {k} {a} {m = node s k' a' l r} (kNotThereL _ y) with compare k k'
-- ... | eq = {!   !}
-- ... | lt = {!   !}
-- ... | gt = {!   !}
-- insertWithInserts {K} {A} ⦃ x ⦄ {f} {k} {a} {m} (kNotThereR x₁ y) = {!   !}
