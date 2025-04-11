module Map.Filter where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.List

open import Map.Balance
open import Map.Construction
open import Map.Map
open import Helpers.Comparable
open import Helpers.Pair

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

private variable
  K V W Q : Set
  

filterWithKey : {{Comparable K}} → (K → V → Bool) → Map K V → Map K V
filterWithKey _ tip = tip
filterWithKey p (node _ kx x l r) with p kx x
...                               | true = link kx x (filterWithKey p l) (filterWithKey p r)
...                               | false = link2 (filterWithKey p l) (filterWithKey p r)

filter : {{Comparable K}} → (V → Bool) → Map K V → Map K V
filter p m = filterWithKey (λ _ x → p x) m

filterKeys : {K V : Set} → {{Comparable K}} → (K → Bool) → Map K V → Map K V
filterKeys p m = filterWithKey (λ k _ → p k) m

record StrictTriple (A B C : Set) : Set where
  field
    st1 : A
    st2 : B
    st3 : C

data Triple (A B C : Set) : Set where
  _,_,_ : A → B → C → Triple A B C

partitionWithKey : {{Comparable K}} → (K → V → Bool) → Map K V → Pair (Map K V) (Map K V)
partitionWithKey p0 t0 = toPair (go p0 t0)
  where
    go : {{Comparable K}} → (K → V → Bool) → Map K V → StrictPair (Map K V) (Map K V)
    go _ tip = tip :*: tip
    go p t@(node _ kx x l r) with (p kx x , go p l , go p r)
    ...                      | (true , ll , rr) = link kx x (fst ll) (fst rr) :*: link2 (snd ll) (snd rr)
    ...                      | (false , ll , rr) = link2 (fst ll) (fst rr) :*: link kx x (snd ll) (snd rr)


partition : {{Comparable K}} → (V → Bool) → Map K V → Pair (Map K V) (Map K V)
partition p m = partitionWithKey (λ _ x → p x) m

takeWhileAntitone : {{Comparable K}} → (K → Bool) → Map K V → Map K V
takeWhileAntitone _ tip = tip
takeWhileAntitone p (node _ kx x l r) with p kx
...                                   | true = link kx x l (takeWhileAntitone p r)
...                                   | _ = takeWhileAntitone p l

dropWhileAntitone : {{Comparable K}} → (K → Bool) → Map K V → Map K V
dropWhileAntitone _ tip = tip
dropWhileAntitone p (node _ kx x l r) with p kx
...                                   | true = dropWhileAntitone p r
...                                   | _ = link kx x (dropWhileAntitone p l) r

spanAntitone : {{Comparable K}} → (K → Bool) → Map K V → Pair (Map K V) (Map K V)
spanAntitone p0 m = toPair (go p0 m)
  where
    go : {{Comparable K}} → (K → Bool) → Map K V → StrictPair (Map K V) (Map K V)
    go _ tip = tip :*: tip
    go p (node _ kx x l r) with (p kx , go p r , go p l)
    ...                    | (true , uv , _) = link kx x l (fst uv) :*: (snd uv)
    ...                    | (false , _ , uv) = fst uv :*: link kx x (snd uv) r

mapMaybeWithKey : {{Comparable K}} → (K → V → Maybe W) → Map K V → Map K W
mapMaybeWithKey _ tip = tip
mapMaybeWithKey f (node _ kx x l r) with f kx x
...                                 | just y = link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
...                                 | nothing = link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)

mapMaybe : {{Comparable K}} → (V → Maybe W) → Map K V → Map K W
mapMaybe f = mapMaybeWithKey (λ _ x → f x)

mapEitherWithKey : {{Comparable K}} → (K → V → Either W Q) → Map K V → Pair (Map K W) (Map K Q)
mapEitherWithKey f0 t0 = toPair (go f0 t0)
  where
    go : {{Comparable K}} → (K → V → Either W Q) → Map K V → StrictPair (Map K W) (Map K Q)
    go _ tip = tip :*: tip
    go f (node _ kx x l r) with (f kx x , go f l , go f r)
    ...                    | (left y , ll , rr) = link kx y (fst ll) (fst rr) :*: link2 (snd ll) (snd rr)
    ...                    | (right z , ll , rr) = link2 (fst ll) (fst rr) :*: link kx z (snd ll) (snd rr)

mapEither : {{Comparable K}} → (V → Either W Q) → Map K V → Pair (Map K W) (Map K Q)
mapEither f m = mapEitherWithKey (λ _ x → f x) m

split : {{Comparable K}} → K → Map K V → Pair (Map K V) (Map K V)
split k0 t0 = toPair (go k0 t0)
  where
    go : {{Comparable K}} → K → Map K V → StrictPair (Map K V) (Map K V)
    go _ tip = tip :*: tip
    go k (node _ kx x l r) with (compare k kx , go k l , go k r)
    ...                    | (lt , ll , _) = (fst ll) :*: link kx x (snd ll) r
    ...                    | (gt , _ , rr) = link kx x l (fst rr) :*: (snd rr)
    ...                    | (eq , _ , _) = l :*: r

splitLookup : {{Comparable K}} → K → Map K V → Triple (Map K V) (Maybe V) (Map K V)
splitLookup k0 m = let record {st1 = l ; st2 = mv ; st3 = r} = go k0 m in (l , mv , r)
  where
    go : {{Comparable K}} → K → Map K V → StrictTriple (Map K V) (Maybe V) (Map K V)
    go k tip = record {st1 = tip ; st2 = nothing ; st3 = tip}
    go k (node _ kx x l r) with compare k kx
    ...                    | lt = let record {st1 = lt' ; st2 = z ; st3 = gt'} = go k l in record {st1 = lt' ; st2 = z ; st3 = link kx x gt' r}
    ...                    | gt = let record {st1 = lt' ; st2 = z ; st3 = gt'} = go k r in record {st1 = link kx x l lt' ; st2 = z ; st3 = gt'}
    ...                    | eq = record {st1 = l ; st2 = just x ; st3 = r}

splitRoot : Map K V → List (Map K V)
splitRoot tip = []
splitRoot (node _ k v l r) = l ∷ singleton k v ∷ r ∷ []