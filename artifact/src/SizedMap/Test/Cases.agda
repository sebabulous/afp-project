module SizedMap.Test.Cases where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Primitive

open import SizedMap.Construction
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Map


private variable
  ℓa ℓb : Level
  ℓA : Set ℓa
  ℓB : Set ℓb
  A K : Set
  x y z : ℓA
  m n : Nat

-- Equality combinators
transport
  : ℓA ≡ ℓB
  → ℓA → ℓB
transport refl a = a

_∵_
  : ℓA
  → ℓA ≡ ℓB
  →     ℓB
a ∵ pf = transport pf a

cong' 
  : (f : ℓA → ℓB)
  →   x ≡   y
  → f x ≡ f y
cong' _ refl = refl

_under_
  : (  x ≡   y) → (f : ℓA → ℓB)
  → (f x ≡ f y)
pf under f = cong' f pf

sym
  : x ≡ y
  → y ≡ x
sym refl = refl

trans : x ≡ y
      →     y ≡ z
      → x ≡     z
trans refl y=z = y=z

_≡⟨_⟩_ : ∀ p {q r : ℓA} → p ≡ q → q ≡ r → p ≡ r
x ≡⟨ x=y ⟩ y=z = trans x=y y=z

_∎ : (a : ℓA) → a ≡ a
a ∎ = refl


data ProofAnd (p₁ : Set) (p₂ : Set) : Set where
  _∧_ : p₁ → p₂ → ProofAnd p₁ p₂

infixl 3 _∧_


KV5a = 5 , "a"
KV5aUpdate = 5 , "5:a"
KV3b = 3 , "b"
KV3bUpdate = 3 , "3:b"
KV7c = 7 , "c"

testEmpty : Map Nat String zero
testEmpty = tip -- fromList []

test53 : Map Nat String 2
test53 = node (Pair.fst KV5a) (Pair.snd KV5a) 
        (node (Pair.fst KV3b) (Pair.snd KV3b) tip tip) tip 
        -- fromList (KV5a ∷ KV3b ∷ [])

test35 : Map Nat String 2
test35 = node (Pair.fst KV3b) (Pair.snd KV3b) 
        tip (node (Pair.fst KV5a) (Pair.snd KV5a) tip tip)
        -- fromList (KV3b ∷ KV5a ∷ []) 

test35update3 : Map Nat String 2
test35update3 = node (Pair.fst KV5a) (Pair.snd KV5a) 
        (node (Pair.fst KV3bUpdate) (Pair.snd KV3bUpdate) tip tip) tip 
        -- fromList (KV3bUpdate ∷ KV5a ∷ []) 

test35update5 : Map Nat String 2
test35update5 = node (Pair.fst KV5aUpdate) (Pair.snd KV5aUpdate) 
        (node (Pair.fst KV3b) (Pair.snd KV3b) tip tip) tip 
        -- fromList (KV3b ∷ KV5aUpdate ∷ []) 

test35update35 : Map Nat String 2
test35update35 = node (Pair.fst KV5aUpdate) (Pair.snd KV5aUpdate) 
        (node (Pair.fst KV3bUpdate) (Pair.snd KV3bUpdate) tip tip) tip 
        -- fromList (KV3b ∷ KV5aUpdate ∷ []) 

test35addX : Map Nat String 2
test35addX = node (Pair.fst KV3b) "bx"
        tip (node (Pair.fst KV5a) "ax" tip tip)

test35add1 : Map Nat String 2
test35add1 = node (Pair.fst KV3b + 1) (Pair.snd KV3b) 
        tip (node (Pair.fst KV5a + 1) (Pair.snd KV5a) tip tip)

test35times2 : Map Nat String 2
test35times2 = node (Pair.fst KV3b * 2) (Pair.snd KV3b) 
        tip (node (Pair.fst KV5a * 2) (Pair.snd KV5a) tip tip)

test57 : Map Nat String 2
test57 = node (Pair.fst KV5a) (Pair.snd KV5a) 
        tip (node (Pair.fst KV7c) (Pair.snd KV7c) tip tip) 
        -- fromList (KV5a ∷ KV7c ∷ [])
        
test537 : Map Nat String 3
test537 = node (Pair.fst KV5a) (Pair.snd KV5a) 
        (node (Pair.fst KV3b) (Pair.snd KV3b) tip tip) 
        (node (Pair.fst KV7c) (Pair.snd KV7c) tip tip) 
        -- fromList (KV5a ∷ KV3b ∷ KV7c ∷ []) 