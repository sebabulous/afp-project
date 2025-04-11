module SizedMap.Map where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Helpers.Provers


private variable
  K A B : Set
  m n m₁ n₁ : Nat
  k : K
  -- ks : List K

_||_ : Bool → Bool → Bool
true || _ = true
_ || true = true
_ || _ = false

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

infixl 3 _&&_



record StrictTriple (A B C : Set) : Set where
  field
    st1 : A
    st2 : B
    st3 : C

data Triple (A B C : Set) : Set where
  _,_,_ : A → B → C → Triple A B C


record Functor (F : (A : Set) → Set): Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B

open Functor {{...}} public

record Applicative (F : Set → Set): Set₁ where
  field
    pure : {A : Set} → A → F A
    _<*>_ : {A B : Set} → F (A → B) → F A → F B

open Applicative {{...}} public

record Monoid (M : Set) : Set where 
  field 
    mempty : M
    mappend : M -> M -> M

open Monoid {{...}} public

data Vec A : Nat → Set where
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (n + 1)

data _∈Vec_ (a : A) : Vec A (suc n) → Set where
  here : {vec : Vec A (suc n)} → a ∈Vec (a ∷ vec)
  there : ∀{a'} → {vec : Vec A (suc n)} → a ∈Vec vec → a ∈Vec (a' ∷ vec)

+zero : m + zero ≡ m
+zero {m = zero} = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero} = refl
+suc {m = suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}

_++_ : {A : Set} → (xs : Vec A m) → (ys : Vec A n) → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

+associative : m + (m₁ + n₁) ≡ m + m₁ + n₁
+associative {m = zero} = refl
+associative {m = suc m} {m₁} {n₁} = cong suc (+associative {_} {m₁} {n₁})

{-# REWRITE +associative #-}

data Map (K : Set) (V : Set) : Nat → Set where
  tip : Map K V zero
  node : K → V → Map K V m → Map K V n → Map K V (suc (m + n))

record Equal (A : Set) : Set where
  field
    equal : A → A → Bool

open Equal {{...}} public

data MapMod K A : Nat → Set where
  modDelete : Map K A n → MapMod K A (suc n)
  modInsert : Map K A (suc n) → MapMod K A n
  modId : Map K A n → MapMod K A n

data MapIns K A : Nat → Set where
  insInsert : Map K A (suc n) → MapIns K A n
  insId : Map K A n → MapIns K A n

data _∈_ {K : Set} (a : A) : Map K A (suc n) → Set where
  here : ∀{k m n}{l : Map K A m}{r : Map K A n} → a ∈ node k a l r
  thereL : ∀{k n a'} → {l : Map K A (suc m)}{r : Map K A n} → a ∈ l → a ∈ (node k a' l r)
  thereR : ∀{k m a'} → {l : Map K A m}{r : Map K A (suc n)} → a ∈ r → a ∈ (node k a' l r)

data _∈k_ {A : Set} (k : K) : Map K A (suc n) → Set where
  here : ∀{a m n}{l : Map K A m}{r : Map K A n} → k ∈k node k a l r
  thereL : ∀{k' n a}{l : Map K A (suc m)}{r : Map K A n} → k ∈k l → k ∈k (node k' a l r)
  thereR : ∀{k' m a}{l : Map K A m}{r : Map K A (suc n)} → k ∈k r → k ∈k (node k' a l r)