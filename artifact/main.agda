module artifact.Main where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

data Ord : Set where
  eq : Ord
  lt : Ord
  gt : Ord

-- source: https://agda.readthedocs.io/en/v2.5.2/language/record-types.html
record Pair (A B : Set): Set where
  constructor _,_
  field
    fst : A
    snd : B

record Comparable (A : Set) : Set where
  field
    compare : A → A → Ord

open Comparable {{...}} public

instance
  NatCmp : Comparable Nat
  compare {{ NatCmp }} zero zero = eq
  compare {{ NatCmp }} zero (suc _) = gt
  compare {{ NatCmp }} (suc _) zero = lt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

--record Functor (F : (A : Set) → Set): Set where
--  field
--    fmap : {A B : Set} → (A → B) → F A → F B

--open Functor {{...}} public

--record Applicative (F : Set → Set): Set where
--  field
--    pure : {A : Set} → A → F A
--    _<*>_ : {A B : Set} → F (A → B) → F A → F B

--open Applicative {{...}} public

data Map (K : Set) (V : Set) : Set where
  tip : Map K V
  node : Nat → K → V → Map K V → Map K V → Map K V

----------------------------------
-- Data.Map functions
----------------------------------

empty : {K : Set}{V : Set} -> Map K V
empty = tip

singleton : {K : Set}{V : Set} -> K -> V -> Map K V
singleton k v = node 1 k v tip tip