
-- Demo code from 2nd AFP Agda lecture
module Demo.Demo2 where

-- Imports & helper defintions
------------------------------

open import Agda.Builtin.Nat as Nat hiding (_<_; _+_)
open import Agda.Builtin.Bool as Bool
open import Agda.Builtin.List as List

module Lib where
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true  then t else _ = t
  if false then _ else e = e

  data _∈_ {A : Set} (a : A) : List A → Set where
    here  : ∀{  xs} → a ∈ (a ∷ xs)
    there : ∀{x xs} → a ∈      xs
                    → a ∈ (x ∷ xs)
open Lib hiding (if_then_else_)

-- Type of well-typed Exp ressions
----------------------------------

data TyTag : Set where
  nat bool : TyTag

module Local (Γ : List TyTag) where
  data Exp : TyTag → Set where
    #   : (n : Nat) → Exp nat
    _+_ : (e1 e2 : Exp nat) → Exp nat
    _<_ : (e1 e2 : Exp nat) → Exp bool
    if_then_else_ : ∀{t} (cond : Exp bool) (e1 e2 : Exp t) → Exp t
    var : ∀{t} → t ∈ Γ → Exp t
open Local

-- Example Exp s
----------------

ex1 : Exp [] nat
ex1 = # 3 + (# 2 + # 1)

ex2 : Exp [] nat
ex2 = if # 10 < (# 3 + # 8) then # 1 else # 2

-- bad3 : Exp [] _
-- bad3 = if # 10 < (# 3 < # 1) then # 1 else # 2

ex4 : Exp (nat ∷ bool ∷ []) nat
ex4 = var here + (if var (there here) then # 1 else # 2)

-- Evaluator
------------

-- "Denotation" of a type tag
⟦_⟧ : TyTag → Set
⟦ nat  ⟧ = Nat
⟦ bool ⟧ = Bool

data Env : List TyTag → Set where
  []  : Env []
  _∷_ : ∀{t ts} → ⟦ t ⟧ → Env ts → Env (t ∷ ts)

lookup : ∀{Γ t} → Env Γ → t ∈ Γ → ⟦ t ⟧
lookup (v ∷ _ )  here     = v
lookup (_ ∷ vs) (there x) = lookup vs x

eval : ∀{Γ t} → Env Γ → Exp Γ t → ⟦ t ⟧
eval ρ (# n) = n
eval ρ (e1 + e2) = eval ρ e1 Nat.+ eval ρ e2
eval ρ (e1 < e2) = eval ρ e1 Nat.< eval ρ e2
eval ρ (if cond then e1 else e2) =
  Lib.if eval ρ cond
    then eval ρ e1
    else eval ρ e2
eval ρ (var x) = lookup ρ x

-- Testing
----------

ev1 = eval [] ex1
ev2 = eval [] ex2
ev4t = eval (100 ∷ true  ∷ []) ex4
ev4f = eval (100 ∷ false ∷ []) ex4