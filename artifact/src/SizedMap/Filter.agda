module SizedMap.Filter where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List

open import SizedMap.Balance
open import SizedMap.Construction
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Query
open import SizedMap.Map

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

private variable
  K A B W Q : Set
  m n : Nat

filterWithKey : {{Comparable K}} → (K → A → Bool) → Map K A n → Σ Nat (Map K A)
filterWithKey _ tip = zero , tip
filterWithKey p (node kx x l r) with p kx x
... | true with filterWithKey p l
...   | record {fst = ls ; snd = lm} with filterWithKey p r
...     | record {fst = rs ; snd = rm} = record {fst = suc (ls + rs) ; snd = link kx x lm rm}
filterWithKey p (node kx x l r) | false with filterWithKey p l
...   | record {fst = ls ; snd = lm} with filterWithKey p r
...     | record {fst = rs ; snd = rm} = record {fst = ls + rs ; snd = link2 lm rm}

filter : {{Comparable K}} → (A → Bool) → Map K A n → Σ Nat (Map K A)
filter p m = filterWithKey (λ _ x → p x) m

filterKeys : {{Comparable K}} → (K → Bool) → Map K A n → Σ Nat (Map K A)
filterKeys p m = filterWithKey (λ k _ → p k) m

splitLookup : {{Comparable K}} → {s : Nat} → K → Map K A s → Σ (Pair Nat Nat) (λ (m , n) → Triple (Map K A m) (Maybe A) (Map K A n))
splitLookup k tip = ((zero , zero) , _,_,_ tip nothing tip)
splitLookup k' (node k a l r) with compare k' k
splitLookup k' (node k a l r) | lt with splitLookup k l
splitLookup k' (node k a l r) | lt | ((m' , n') , (_,_,_ lt' z gt')) = ((m' , suc (n' + size r)) , (_,_,_ lt' z (link k a gt' r)))
splitLookup k' (node k a l r) | gt with splitLookup k r
splitLookup k' (node k a l r) | gt | ((m' , n') , (_,_,_ lt' z gt')) = ((suc (size l + m') , n') , (_,_,_ (link k a l lt') z gt'))
splitLookup k' (node k a l r) | eq = ((size l , size r) , (_,_,_ l (just a) r))