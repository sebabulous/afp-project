module Map.Map where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality


private variable
  K A B : Set
  m n : Nat

_||_ : Bool → Bool → Bool
true || _ = true
_ || true = true
_ || _ = false

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

infixl 3 _&&_

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

record StrictTriple (A B C : Set) : Set where
  field
    st1 : A
    st2 : B
    st3 : C

data Triple (A B C : Set) : Set where
  _,_,_ : A → B → C → Triple A B C

record Comparable (A : Set) : Set where
  field
    compare : A → A → Ord

open Comparable {{...}} public

instance
  NatCmp : Comparable Nat
  compare {{ NatCmp }} zero zero = eq
  compare {{ NatCmp }} zero (suc _) = lt
  compare {{ NatCmp }} (suc _) zero = gt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

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

-- data Map (K : Set) (V : Set) : Set where
--   tip : Map K V
--   node : Nat → K → V → Map K V → Map K V → Map K V
data Map (K : Set) (V : Set) : Nat → Set where
  tip : Map K V zero
  node : {m n : Nat} → Nat → K → V → Map K V m → Map K V n → Map K V (suc (m + n))

record Equal (A : Set) : Set where
  field
    equal : A → A → Bool

open Equal {{...}} public

-- instance
--   EqMap : ∀{n} {K V : Set} → {{Equal K}} → {{Equal V}} → Equal (Map K V n)
--   equal {{ EqMap }} tip tip = true
--   equal {{ EqMap }} (node s k v l r) (node s' k' v' l' r') = s == s' && equal k k' && equal v v' && equal l l' && equal r r'
--   equal {{ EqMap }} _ _ = false



data MapMod K A : Nat → Set where
  modDelete : Map K A n → MapMod K A (suc n)
  modInsert : Map K A (suc n) → MapMod K A n
  modId : Map K A n → MapMod K A n

data MapIns K A : Nat → Set where
  insInsert : Map K A (suc n) → MapIns K A n
  insId : Map K A n → MapIns K A n