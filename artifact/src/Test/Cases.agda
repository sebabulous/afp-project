module Test.Cases where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Map.Construction
open import Map.Map

private variable
  ℓa ℓb : Level
  A : Set ℓa
  B : Set ℓb
  x y z : A

-- Equality combinators
transport
  : A ≡ B
  → A → B
transport refl a = a

_∵_
  : A
  → A ≡ B
  →     B
a ∵ pf = transport pf a

cong 
  : (f : A → B)
  →   x ≡   y
  → f x ≡ f y
cong _ refl = refl

_under_
  : (  x ≡   y) → (f : A → B)
  → (f x ≡ f y)
pf under f = cong f pf

sym
  : x ≡ y
  → y ≡ x
sym refl = refl

trans : x ≡ y
      →     y ≡ z
      → x ≡     z
trans refl y=z = y=z

_≡⟨_⟩_ : ∀ p {q r : A} → p ≡ q → q ≡ r → p ≡ r
x ≡⟨ x=y ⟩ y=z = trans x=y y=z

_∎ : (a : A) → a ≡ a
a ∎ = refl

_++_ : (l : List A) → (r : List A) → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ l ++ r

[]++≡id : (as : List A) → [] ++ as ≡ as
[]++≡id as = refl

id≡++[] : (as : List A) → as ++ [] ≡ as
id≡++[] [] = refl
id≡++[] (x ∷ as) = cong (x ∷_) (id≡++[] as)

-- Test cases
KV5a = 5 , "a"
KV5aUpdate = 5 , "5:a"
KV3b = 3 , "b"
KV3bUpdate = 3 , "3:b"
KV7c = 7 , "c"

testEmpty : Map Nat String
testEmpty = fromList []

test53 : Map Nat String
test53 = fromList (KV5a ∷ KV3b ∷ [])

test35 : Map Nat String
test35 = fromList (KV3b ∷ KV5a ∷ []) 

test35update3 : Map Nat String
test35update3 = fromList (3 , "3:b" ∷ KV5a ∷ []) 

test35update5 : Map Nat String
test35update5 = fromList (KV3b ∷ KV5aUpdate ∷ []) 

test35update35 : Map Nat String
test35update35 =  fromList (KV3bUpdate ∷ KV5aUpdate ∷ []) 

test35addX : Map Nat String
test35addX = fromList (3 , "bx" ∷ 5 , "ax" ∷ [])

test35add1 : Map Nat String
test35add1 = fromList ((Pair.fst KV3b + 1) , Pair.snd KV3b ∷ (Pair.fst KV5a + 1) , Pair.snd KV5a ∷ [])

test35times2 : Map Nat String
test35times2 = fromList ((Pair.fst KV3b * 2) , Pair.snd KV3b ∷ (Pair.fst KV5a * 2) , Pair.snd KV5a ∷ [])

test57 : Map Nat String
test57 = fromList (KV5a ∷ KV7c ∷ [])
        
test537 : Map Nat String
test537 = fromList (KV5a ∷ KV3b ∷ KV7c ∷ [])