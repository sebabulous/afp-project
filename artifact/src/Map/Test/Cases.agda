module Map.Test.Cases where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Map.Construction
open import Map.Map
open import Map.Balance
open import Map.Query
open import Helpers.Comparable
open import Helpers.Pair
open import Helpers.Void


private variable
  ℓa ℓb : Level
  A : Set ℓa
  B : Set ℓb
  K : Set
  V : Set
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

odd  : Nat → Bool
odd zero     = false
odd (suc zero) = true
odd (suc (suc n))  = odd n

[]++≡id : (as : List A) → [] ++ as ≡ as
[]++≡id as = refl

id≡++[] : (as : List A) → as ++ [] ≡ as
id≡++[] [] = refl
id≡++[] (x ∷ as) = cong (x ∷_) (id≡++[] as)

insertWith : {{Comparable K}} → (A → A → A) → K → A → List (Pair K A) → List (Pair K A)
insertWith _ k' a' [] = (k' , a') ∷ []
insertWith f k' a' ((k , a) ∷ xs) with compare k' k
insertWith f k' a' ((k , a) ∷ xs) | eq = (k , f a' a) ∷ xs
insertWith f k' a' ((k , a) ∷ xs) | _ = (k , a) ∷ insertWith f k' a' xs

combineWith : {{Comparable K}} → (A → A → A) → List (Pair K A) → List (Pair K A) → List (Pair K A)
combineWith _ [] ys = ys
combineWith f ((k , a) ∷ xs) ys = combineWith f xs (insertWith f k a ys)

insertWithKey : {{Comparable K}} → (K → A → A → A) → K → A → List (Pair K A) → List (Pair K A)
insertWithKey _ k' a' [] = (k' , a') ∷ []
insertWithKey f k' a' ((k , a) ∷ xs) with compare k' k
insertWithKey f k' a' ((k , a) ∷ xs) | eq = (k , f k a' a) ∷ xs
insertWithKey f k' a' ((k , a) ∷ xs) | _ = (k , a) ∷ insertWithKey f k' a' xs

combineWithKey : {{Comparable K}} → (K → A → A → A) → List (Pair K A) → List (Pair K A) → List (Pair K A)
combineWithKey _ [] ys = ys
combineWithKey f ((k , a) ∷ xs) ys = combineWithKey f xs (insertWithKey f k a ys)

insertPair : Pair Nat Nat → List (Pair Nat Nat) → List (Pair Nat Nat)
insertPair (k' , a') [] = (k' , a') ∷ [] 
insertPair (k' , a') ((k , a) ∷ xs) with compare k' k
insertPair (k' , a') ((k , a) ∷ xs) | eq = (k , a') ∷ xs
insertPair (k' , a') ((k , a) ∷ xs) | gt = (k , a) ∷ insertPair (k' , a') xs
insertPair (k' , a') ((k , a) ∷ xs) | lt = (k' , a') ∷ (k , a) ∷ xs

sortKeysAsc : List (Pair Nat Nat) → List (Pair Nat Nat)
sortKeysAsc [] = []
sortKeysAsc (x ∷ xs) = insertPair x (sortKeysAsc xs)

takeList : Nat → List A → List A
takeList zero _ = []
takeList _ [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

dropList : Nat → List A → List A
dropList zero xs = xs
dropList _ [] = []
dropList (suc n) (x ∷ xs) = dropList n xs

-- Test cases
KV5a = 5 , "a"
KV5aUpdate = 5 , "5:a"
KV3b = 3 , "b"
KV3bUpdate = 3 , "3:b"
KV7c = 7 , "c"

data isNode {k : K} {v : V} : Map K V → Set where
  toldYa : ∀{s k v l r} → isNode (node s k v l r)

topKey : ∀{K V} → {k : K} → {v : V} → (m : Map K V) → {isNode {_} {_} {k} {v} m} → K
topKey (node _ k _ _ _) = k

topVal : ∀{K V} → {k : K} → {v : V} → (m : Map K V) → {isNode {_} {_} {k} {v} m} → V
topVal (node _ _ v _ _) = v

getL : ∀{K V} → {k : K} → {v : V} → (m : Map K V) → {isNode {_} {_} {k} {v} m} → Map K V
getL (node _ _ _ l _) = l

getR : ∀{K V} → {k : K} → {v : V} → (m : Map K V) → {isNode {_} {_} {k} {v} m} → Map K V
getR (node _ _ _ _ r) = r

data _∈_ (x : Pair K V) : Map K V → Set where
  here : ∀{s l r} → let (k , v) = x in x ∈ node s k v l r
  thereL : ∀{s k v l r} → x ∈ l → x ∈ node s k v l r
  thereR : ∀{s k v l r} → x ∈ r → x ∈ node s k v l r

data _∈k_ {v : V} (k : K) : Map K V → Set where
  kHere : ∀{s l r} → k ∈k node s k v l r
  kThereL : ∀{s v k' l r} → _∈k_ {_} {_} {v} k l → k ∈k node s k' v l r
  kThereR : ∀{s v k' l r} → _∈k_ {_} {_} {v} k r → k ∈k node s k' v l r

data _≠_ {V : Set} (x : V) : V → Set where
  ne : ∀{y} → (x ≡ y → ⊥) → x ≠ y


testEmpty : Map Nat String
testEmpty = fromList []

test2Nat : Map Nat Nat
test2Nat = fromList (2 , 2 ∷ []) 

test15Nat : Map Nat Nat
test15Nat = fromList (1 , 1 ∷ 5 , 5 ∷ []) 

test15SucNat : Map Nat Nat
test15SucNat = fromList (1 , 2 ∷ 5 , 6 ∷ []) 

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
test537 = node 3 (Pair.fst KV5a) (Pair.snd KV5a) 
        (node 1 (Pair.fst KV3b) (Pair.snd KV3b) tip tip) 
        (node 1 (Pair.fst KV7c) (Pair.snd KV7c) tip tip) 