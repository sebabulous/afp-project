module Map.Map where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

_||_ : Bool → Bool → Bool
true || _ = true
_ || true = true
_ || _ = false

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

_++_ : {A : Set} → (l : List A) → (r : List A) → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ l ++ r

infixl 3 _&&_

maybe : {A B : Set} → B → (A -> B) → Maybe A → B
maybe n _ nothing  = n
maybe _ f (just x) = f x

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
  compare {{ NatCmp }} zero (suc _) = lt
  compare {{ NatCmp }} (suc _) zero = gt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

record Functor (F : (A : Set) → Set): Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B

open Functor {{...}} public

instance
  MaybeFunctor : Functor Maybe
  fmap ⦃ MaybeFunctor ⦄ f (just x) = just (f x)
  fmap ⦃ MaybeFunctor ⦄ f nothing = nothing

record Applicative (F : Set → Set): Set₁ where
  field
    pure : {A : Set} → A → F A
    _<*>_ : {A B : Set} → F (A → B) → F A → F B
    liftA3 : {A B C D : Set} → (A → B → C → D) → F A → F B → F C → F D

open Applicative {{...}} public

instance
  MaybeApplicative : Applicative Maybe
  pure ⦃ MaybeApplicative ⦄ a = just a
  _<*>_ ⦃ MaybeApplicative ⦄ (just f) m = fmap f m
  _<*>_ ⦃ MaybeApplicative ⦄ nothing m = nothing
  liftA3 ⦃ MaybeApplicative ⦄ f a b c = (fmap f a <*> b) <*> c 

record Monoid (M : Set) : Set where 
  field 
    mempty : M
    mappend : M -> M -> M

open Monoid {{...}} public

instance
  NatMonoid : Monoid Nat
  mempty {{ NatMonoid }} = zero
  mappend {{ NatMonoid }} zero n = n
  mappend {{ NatMonoid }} (suc x) n = suc (mappend x n)

data Map (K : Set) (V : Set) : Set where
  tip : Map K V
  node : Nat → K → V → Map K V → Map K V → Map K V

record Equal (A : Set) : Set where
  field
    equal : A → A → Bool

open Equal {{...}} public

instance
  EqMap : {K V : Set} → {{Equal K}} → {{Equal V}} → Equal (Map K V)
  equal {{ EqMap }} tip tip = true
  equal {{ EqMap }} (node s k v l r) (node s' k' v' l' r') = s == s' && equal k k' && equal v v' && equal l l' && equal r r'
  equal {{ EqMap }} _ _ = false