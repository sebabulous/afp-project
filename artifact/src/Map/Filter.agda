module Map.Filter where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List

open import Map.Balance
open import Map.Construction
open import Map.Query
open import Map.Map

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

private variable
  K A B W Q : Set
  m n : Nat

-- https://agda.github.io/agda-stdlib/v2.1/Data.Vec.html
-- record Map≤ (K : Set) (A : Set) (n : Nat) : Set where
--   field
--     {mapLen} : Nat
--     map : Map K A mapLen
--     .bound : mapLen < n

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

-- -- restrictKeys : {{Comparable K}} → Map K A → Set K → Map K A

-- -- withoutKeys : {{Comparable K}} → Map K A → Set K → Map K A


-- partitionWithKey : {{Comparable K}} → {s : Nat} → (K → A → Bool) → Map K A s → {m + n ≡ s} → Pair (Map K A m) (Map K A n)
-- partitionWithKey p0 t0 = toPair (go p0 t0)
--   where
--     go : {{Comparable K}} → (K → A → Bool) → Map K A → StrictPair (Map K A) (Map K A)
--     go _ tip = tip :*: tip
--     go p t@(node _ kx x l r) with (p kx x , go p l , go p r)
--     ...                      | (true , ll , rr) = link kx x (fst ll) (fst rr) :*: link2 (snd ll) (snd rr)
--     ...                      | (false , ll , rr) = link2 (fst ll) (fst rr) :*: link kx x (snd ll) (snd rr)


-- partition : {{Comparable K}} → (A → Bool) → Map K A → Pair (Map K A) (Map K A)
-- partition p m = partitionWithKey (λ _ x → p x) m

-- takeWhileAntitone : {{Comparable K}} → (K → Bool) → Map K A → Map K A
-- takeWhileAntitone _ tip = tip
-- takeWhileAntitone p (node _ kx x l r) with p kx
-- ...                                   | true = link kx x l (takeWhileAntitone p r)
-- ...                                   | _ = takeWhileAntitone p l

-- dropWhileAntitone : {{Comparable K}} → (K → Bool) → Map K A → Map K A
-- dropWhileAntitone _ tip = tip
-- dropWhileAntitone p (node _ kx x l r) with p kx
-- ...                                   | true = dropWhileAntitone p r
-- ...                                   | _ = link kx x (dropWhileAntitone p l) r

-- spanAntitone : {{Comparable K}} → (K → Bool) → Map K A → Pair (Map K A) (Map K A)
-- spanAntitone p0 m = toPair (go p0 m)
--   where
--     go : {{Comparable K}} → (K → Bool) → Map K A → StrictPair (Map K A) (Map K A)
--     go _ tip = tip :*: tip
--     go p (node _ kx x l r) with (p kx , go p r , go p l)
--     ...                    | (true , uv , _) = link kx x l (fst uv) :*: (snd uv)
--     ...                    | (false , _ , uv) = fst uv :*: link kx x (snd uv) r

-- mapMaybeWithKey : {{Comparable K}} → (K → A → Maybe W) → Map K A → Map K W
-- mapMaybeWithKey _ tip = tip
-- mapMaybeWithKey f (node _ kx x l r) with f kx x
-- ...                                 | just y = link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
-- ...                                 | nothing = link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)

-- mapMaybe : {{Comparable K}} → (A → Maybe W) → Map K A → Map K W
-- mapMaybe f = mapMaybeWithKey (λ _ x → f x)

-- mapEitherWithKey : {{Comparable K}} → (K → A → Either W Q) → Map K A → Pair (Map K W) (Map K Q)
-- mapEitherWithKey f0 t0 = toPair (go f0 t0)
--   where
--     go : {{Comparable K}} → (K → A → Either W Q) → Map K A → StrictPair (Map K W) (Map K Q)
--     go _ tip = tip :*: tip
--     go f (node _ kx x l r) with (f kx x , go f l , go f r)
--     ...                    | (left y , ll , rr) = link kx y (fst ll) (fst rr) :*: link2 (snd ll) (snd rr)
--     ...                    | (right z , ll , rr) = link2 (fst ll) (fst rr) :*: link kx z (snd ll) (snd rr)

-- mapEither : {{Comparable K}} → (A → Either W Q) → Map K A → Pair (Map K W) (Map K Q)
-- mapEither f m = mapEitherWithKey (λ _ x → f x) m

-- split : {{Comparable K}} → K → Map K A → Pair (Map K A) (Map K A)
-- split k0 t0 = toPair (go k0 t0)
--   where
--     go : {{Comparable K}} → K → Map K A → StrictPair (Map K A) (Map K A)
--     go _ tip = tip :*: tip
--     go k (node _ kx x l r) with (compare k kx , go k l , go k r)
--     ...                    | (lt , ll , _) = (fst ll) :*: link kx x (snd ll) r
--     ...                    | (gt , _ , rr) = link kx x l (fst rr) :*: (snd rr)
--     ...                    | (eq , _ , _) = l :*: r

splitLookup : {{Comparable K}} → {s : Nat} → K → Map K A s → Σ (Pair Nat Nat) (λ (m , n) → Triple (Map K A m) (Maybe A) (Map K A n))
splitLookup k tip = ((zero , zero) , _,_,_ tip nothing tip)
splitLookup k' (node k a l r) with compare k' k
splitLookup k' (node k a l r) | lt with splitLookup k l
splitLookup k' (node k a l r) | lt | ((m' , n') , (_,_,_ lt' z gt')) = ((m' , suc (n' + size r)) , (_,_,_ lt' z (link k a gt' r)))
splitLookup k' (node k a l r) | gt with splitLookup k r
splitLookup k' (node k a l r) | gt | ((m' , n') , (_,_,_ lt' z gt')) = ((suc (size l + m') , n') , (_,_,_ (link k a l lt') z gt'))
splitLookup k' (node k a l r) | eq = ((size l , size r) , (_,_,_ l (just a) r))
-- splitLookup k0 m = let record {st1 = l ; st2 = mv ; st3 = r} = go k0 m in (l , mv , r)
--   where
--     go : {{Comparable K}} → K → Map K A → StrictTriple (Map K A) (Maybe A) (Map K A)
--     go k tip = record {st1 = tip ; st2 = nothing ; st3 = tip}
--     go k (node _ kx x l r) with compare k kx
--     ...                    | lt = let record {st1 = lt' ; st2 = z ; st3 = gt'} = go k l in record {st1 = lt' ; st2 = z ; st3 = link kx x gt' r}
--     ...                    | gt = let record {st1 = lt' ; st2 = z ; st3 = gt'} = go k r in record {st1 = link kx x l lt' ; st2 = z ; st3 = gt'}
--     ...                    | eq = record {st1 = l ; st2 = just x ; st3 = r}

-- splitRoot : Map K A → List (Map K A)
-- splitRoot tip = []
-- splitRoot (node _ k v l r) = l ∷ singleton k v ∷ r ∷ [] 