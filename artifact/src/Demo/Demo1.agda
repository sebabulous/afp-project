
-- Demo code from 1st AFP Agda lecture
module Demo.Demo1 where

-- Installation
---------------

-- https://github.com/agda/agda/releases/tag/v2.7.0.1

-- $PATH

-- $Agda_datadir

-- banacorn.agda-mode

-- Interactive development
--------------------------

open import Agda.Builtin.Nat

fib : Nat -> Nat
fib zero = 1
fib (suc x) = suc x * fib x

-- C-c C-l    -- Load file
-- C-c C-f    -- Forwards to next hole
-- C-c C-b    -- Back to previous hole
-- C-c C-c    -- Case split
-- C-c C-SPC  -- Give expression to fill hole

-- Testing
----------

f100 = fib 100
-- C-c C-n    -- Normalize

-- Unicode
----------

-- \ - >
-- \ : :

-- Lists
--------

open import Agda.Builtin.List

l1 = 1 ∷ 2 ∷ 3 ∷ []
l2 = 4 ∷ 5 ∷ []

-- Named parameters, polymorphism
---------------------------------

-- append : List Nat → List Nat → List Nat
-- append : (xs : List Nat) → (ys : List Nat) → List Nat
-- append : (A : Set) → (xs : List A) → (ys : List A) → List A
append : {A : Set} → (xs : List A) → (ys : List A) → List A
append [] ys       = ys
append (x ∷ xs) ys = x ∷ append xs ys

-- C-c C-c    -- Introduce function arguments
-- C-c C-.    -- Inspect hole

l3 = append l1 l2

-- Infix operators, helper function extraction
----------------------------------------------

_++_ = append

open import Agda.Builtin.Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then t else _ = t
if false then _ else e = e

infixr 4 if_then_else_

insert : Nat → List Nat → List Nat
insert n []       = n ∷ [] 
insert n (x ∷ xs) =
    if n < x
    then n ∷ x ∷ xs
    else x ∷ insert x xs

sort : List Nat → List Nat
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

-- C-c C-h    -- Helper function type

l4 = sort (5 ∷ 7 ∷ 2 ∷ 3 ∷ 9 ∷ [])

-- Custom data types
--------------------

data Tree (A : Set) : Set where
  leaf : A → Tree A
  _:|:_ : Tree A → Tree A → Tree A

t1 = (leaf 1 :|: leaf 2) :|: leaf 3

flatten : {A : Set} → Tree A → List A
flatten (leaf x)    = x ∷ []
flatten (t1 :|: t2) = flatten t1 ++ flatten t2

-- Libraries
------------

-- .agda-lib

-- open import Function.Base

-- _ = {! _∘_ !}

-- C-c C-w  -- Why in scope