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

-- Test cases
KV5a = 5 , "a"
KV5aUpdate = 5 , "5:a"
KV3b = 3 , "b"
KV3bUpdate = 3 , "3:b"
KV7c = 7 , "c"

data ⊥ : Set where

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

data _∈minV_ (x : Pair K V) : (MinView K V) → Set where
--   here : ∀{m} → let record {fst = k ; snd = v} = x in x ∈minV (record {minK = k ; minV = v ; minM = m})
  here : ∀{m} → let record {fst = k ; snd = v} = x in x ∈minV (minview k v m)
--   there : ∀{k v m} → x ∈ m → x ∈minV (record {minK = k ; minV = v ; minM = m})
  there : ∀{k v m} → x ∈ m → x ∈minV (minview k v m)

data _∈maxV_ (x : Pair K V) : (MaxView K V) → Set where
--   here : ∀{m} → let record {fst = k ; snd = v} = x in x ∈maxV (record {maxK = k ; maxV = v ; maxM = m})
  here : ∀{m} → let record {fst = k ; snd = v} = x in x ∈maxV (maxview k v m)
--   there : ∀{k v m} → x ∈ m → x ∈maxV (record {maxK = k ; maxV = v ; maxM = m})
  there : ∀{k v m} → x ∈ m → x ∈maxV (maxview k v m)

data _≠_ {V : Set} (x : V) : V → Set where
  ne : ∀{y} → (x ≡ y → ⊥) → x ≠ y

data _∉_ (x : Pair K V) : Map K V → Set where
  notHere : x ∉ tip
  notThereL : ∀{s k v l r} → let record {fst = k' ; snd = v'} = x in k ≠ k' → x ∉ l → x ∉ node s k v l r
  notThereR : ∀{s k v l r} → let record {fst = k' ; snd = v'} = x in k ≠ k' → x ∉ r → x ∉ node s k v l r

data _∉k_ {v : V} (k : K) : Map K V → Set where
  kNotHere : k ∉k tip
  kNotThereL : ∀{s k' v l r} → k ≠ k' → _∉k_ {_} {_} {v} k l → k ∉k node s k' v l r
  kNotThereR : ∀{s k' v l r} → k ≠ k' → _∉k_ {_} {_} {v} k r → k ∉k node s k' v l r


keyGivesVal : {{_ : Comparable K}} → {k : K} → {a : A} → {m : Map K A} → _∈k_ {_} {_} {a} k m → lookup k m ≡ just a
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {tip} ()
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} kHere with compare k' k
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} kHere | eq = refl
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} kHere | lt = {!   !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} kHere | gt = {!   !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereL prf) with compare k' k
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereL prf) | eq = {!   !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereL prf) | lt = keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {l} {! prf  !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereL prf) | gt = {!   !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereR prf) with compare k' k
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereR prf) | eq = {!   !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereR prf) | lt = {!   !}
keyGivesVal {K} {A} ⦃ x ⦄ {k'} {a'} {node s k a l r} (kThereR prf) | gt = {!   !}


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
        -- fromList (KV5a ∷ KV3b ∷ KV7c ∷ [])  

