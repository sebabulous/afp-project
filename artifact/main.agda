open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Maybe

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

data Ord : Set where
  eq : Ord
  lt : Ord
  gt : Ord

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
  compare {{ NatCmp }} zero (suc _) = gt
  compare {{ NatCmp }} (suc _) zero = lt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

record Functor (F : (A : Set) → Set): Set where
  field
    fmap : {A B : Set} → (A → B) → F A → F B

open Functor {{...}} public


data Map (K : Set) (V : Set) : Set where
  tip : Map K V
  node : Nat → K → V → Map K V → Map K V → Map K V

size : {K : Set}{V : Set} → Map K V → Nat
size tip = 0
size (node s _ _ _ _) = s

isValid : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → Bool
isValid tip = true
isValid (node s k' v' l r) with size l + size r
isValid (node s k' v' l r) | s' = ((s' + 1 == s) && isValid l) && isValid r

----------------------------------
-- Data.Map functions
----------------------------------

empty : {K : Set}{V : Set} -> Map K V
empty = tip

singleton : {K : Set}{V : Set} -> K -> V -> Map K V
singleton k v = node 1 k v tip tip

insert : {K : Set} → {V : Set} → {{Comparable K}} → K → V → Map K V → Map K V
insert k v tip = node 1 k v tip tip
insert k v (node s k' v' l r) with compare k k'
insert k v (node s k' v' l r) | eq = node s k v l r
insert k v (node s k' v' l r) | lt = let l' = insert k v l in node (1 + size l' + size r) k' v' l' r
insert k v (node s k' v' l r) | gt = let r' = insert k v r in node (1 + size l + size r') k' v' l r'

insertWith : {K : Set} → {V : Set} → {{Comparable K}} → (V -> V -> V) -> K → V → Map K V → Map K V
insertWith f k v tip = node 1 k v tip tip
insertWith f k v (node s k' v' l r) with compare k k'
insertWith f k v (node s k' v' l r) | eq = node s k (f v v') l r
insertWith f k v (node s k' v' l r) | lt = let l' = insertWith f k v l in node (1 + size l' + size r) k' v' l' r
insertWith f k v (node s k' v' l r) | gt = let r' = insertWith f k v r in node (1 + size l + size r') k' v' l r'

insertWithKey : {K : Set} → {V : Set} → {{Comparable K}} → (K -> V -> V -> V) -> K → V → Map K V → Map K V
insertWithKey f k v tip = node 1 k v tip tip
insertWithKey f k v (node s k' v' l r) with compare k k'
insertWithKey f k v (node s k' v' l r) | eq = node s k (f k v v') l r
insertWithKey f k v (node s k' v' l r) | lt = let l' = insertWithKey f k v l in node (1 + size l' + size r) k' v' l' r
insertWithKey f k v (node s k' v' l r) | gt = let r' = insertWithKey f k v r in node (1 + size l + size r') k' v' l r'

----------------------------------
-- Deletion/ Update
----------------------------------

data StrictPair (A B : Set): Set where
  _:*:_ : A → B → StrictPair A B

infixr 1 _:*:_

toPair : {A B : Set} → StrictPair A B → Pair A B
toPair (a :*: b) = (a , b)


if_then_else_ : {A : Set} → Bool → A → A → A
if_then_else_ true a _ = a
if_then_else_ false _ a = a

delta = 3
ratio = 2

balance : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
balance k v tip tip = node 1 k v tip tip

balance k v tip r@(node _ _ _ tip tip) = node 2 k v tip r
balance k v tip r@(node _ rk rv tip rr@(node _ _ _ _ _)) = node 3 rk rv (node 1 k v tip tip) rr
balance k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = node 3 rlk rlv (node 1 k v tip tip) (node 1 rk rv tip tip)
balance k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) with compare rls (ratio * rrs)
balance k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | lt = node (1 + rs) rk rv (node (1 + rls) k v tip rl) rr
balance k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | _ = node (1 + rs) rlk rlv (node (1 + size rll) k v tip rll) (node (1 + rrs + size rlr) rk rv rlr rr)

balance k v l@(node ls lk lv tip tip) tip = node 2 k v l tip
balance k v (node ls lk lv tip (node _ lrk lrv _ _)) tip = node 3 lrk lrv (node 1 lk lv tip tip) (node 1 k v tip tip)
balance k v (node ls lk lv ll@(node _ _ _ _ _) tip) tip = node 3 lk lv ll (node 1 k v tip tip)
balance k v (node ls lk lv (node lls _ _ _ _) (node lrs lrk lrv lrl lrr)) tip with compare lrs (ratio * lls)
balance k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) tip | lt = node (1 + ls) lk lv ll (node (1 + lrs) k v lr tip)
balance k v (node ls lk lv ll@(node lls _ _ _ _) (node lrs lrk lrv lrl lrr)) tip | _ = node (1 + ls) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + size lrr) k v lrr tip)

balance k v (node ls lk lv ll lr) (node rs rk rv rl rr) with (compare rs (delta * ls), compare ls (delta * rs))
balance k v l@(node ls lk lv ll lr) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | (gt,_) = if rls < ratio * rrs then node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr else node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
balance k v l@(node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs rk rv rl rr) | (_,gt) = if lrs < ratio * lls then node (1 + ls + rs) lk lv ll (node (1 + rs + lrs) k v lr r) else node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
balance k v l@(node ls lk lv _ _) r@(node rs rk rv rl rr) | _ = node (1 + ls + rs) k v l r




balanceL : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
balanceL k v tip tip = node 1 k v tip tip

balanceL k v l@(node _ _ _ tip tip) tip = node 2 k v l tip
balanceL k v (node _ lk lv tip (node _ lrk lrv _ _)) tip = node 3 lrk lrv (node 1 lk lv tip tip) (node 1 k v tip tip)
balanceL k v (node _ lk lv ll@(node _ _ _ _ _) tip) tip = node 3 lk lv ll (node 1 k v tip tip)
balanceL k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) tip with compare lrs (ratio * lls)
...                                                                                  | lt = node (1 + ls) lk lv ll (node (1 + lrs) k v lr tip)
...                                                                                  | _ = node (1 + ls) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + size lrr) k v lrr tip)

balanceL k v tip r@(node rs _ _ _ _) = node (1 + rs) k v tip r
balanceL k v (node ls lk lv ll lr) (node rs _ _ _ _) with compare rs (delta * ls)
balanceL k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs _ _ _ _) | gt = if lrs < ratio * lls then node (1 + ls + rs) lk lv ll (node (1 + rs + lrs) k v lr r) else node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
balanceL k v (node ls lk lv _ _) (node rs _ _ _ _) | gt = {!   !}
balanceL k v l@(node ls lk lv ll lr) r@(node rs _ _ _ _) | _ = node (1 + ls + rs) k v l r


balanceR : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
balanceR k v tip tip = node 1 k v tip tip

balanceR k v tip r@(node _ _ _ tip tip) = node 2 k v tip r
balanceR k v tip (node _ rk rv tip rr@(node _ _ _ _ _)) = node 3 rk rv (node 1 k v tip tip) rr
balanceR k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = node 3 rlk rlv (node 1 k v tip tip) (node 1 rk rv tip tip)
balanceR k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) with rls < ratio * rrs
...                                                                                  | true = node (1 + rs) rk rv (node (1 + rls) k v tip rl) rr
...                                                                                  | false = node (1 + rs) rlk rlv (node (1 + size rll) k v tip rll) (node (1 + rrs + size rlr) rk rv rlr rr)

balanceR k v l@(node ls _ _ _ _) tip = node (1 + ls) k v l tip
balanceR k v (node ls _ _ _ _) (node rs _ _ _ _) with compare rs (delta * ls)
balanceR k v l@(node ls _ _ _ _) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | gt = if rls < ratio * rrs then node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr else node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
balanceR k v (node ls _ _ _ _) (node _ _ _ _ _) | gt = {!   !}
balanceR k v l@(node ls _ _ _ _) r@(node rs _ _ _ _) | _ = node (1 + ls + rs) k v l r


record MinView (K : Set) (V : Set): Set where
  field
    minK : K
    minV : V
    minM : Map K V

record MaxView (K : Set) (V : Set): Set where
  field
    maxK : K
    maxV : V
    maxM : Map K V

minViewSure : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → MinView K V
minViewSure k v tip r = record {minK = k ; minV = v ; minM = r}
minViewSure k v (node _ kl vl ll lr) r with minViewSure kl vl ll lr
...                                    | record {minK = km ; minV = vm ; minM = l'} = record {minK = km ; minV = vm ; minM = balanceR k v l' r}

maxViewSure : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → MaxView K V
maxViewSure k v l tip = record {maxK = k ; maxV = v ; maxM = l}
maxViewSure k v l (node _ kr vr rl rr) with maxViewSure kr vr rl rr
...                                    | record {maxK = km ; maxV = vm ; maxM = r'} = record {maxK = km ; maxV = vm ; maxM = balanceL k v l r'}

glue : {K V : Set} → {{Comparable K}} → Map K V → Map K V → Map K V
glue tip r = r
glue l tip = l
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) with compare sl sr
...                                                  | gt = let record {maxK = km ; maxV = m ; maxM = l'} = maxViewSure kl vl ll lr in balanceR km m l' r
...                                                  | _ = let record {minK = km ; minV = m ; minM = r'} = minViewSure kr vr rl rr in balanceL km m l r'



delete : {K V : Set} → {{Comparable K}} → K → Map K V → Map K V
delete _ tip = tip
delete k (node _ k' v l r) with compare k k'
...                       | lt = balanceR k' v (delete k l) r
...                       | gt = balanceL k' v l (delete k r)
...                       | eq = glue l r

adjustWithKey : {K V : Set} → {{Comparable K}} → (K → V → V) → K → Map K V → Map K V
adjustWithKey _ _ tip = tip
adjustWithKey f k (node s k' v l r) with compare k k'
...                                 | lt = node s k' v (adjustWithKey f k l) r
...                                 | gt = node s k' v l (adjustWithKey f k r)
...                                 | eq = node s k' (f k' v) l r

adjust : {K V : Set} → {{Comparable K}} → (V → V) → K → Map K V → Map K V
adjust f = adjustWithKey (λ _ v → f v)

updateWithKey : {K V : Set} → {{Comparable K}} → (K → V → Maybe V) → K → Map K V → Map K V
updateWithKey _ _ tip = tip
updateWithKey f k (node s k' v l r) with compare k k'
...                                 | lt = balanceR k' v (updateWithKey f k l) r
...                                 | gt = balanceL k' v l (updateWithKey f k r)
...                                 | eq with f k' v
...                                      | just v' = node s k' v' l r
...                                      | nothing = glue l r

update : {K V : Set} → {{Comparable K}} → (V → Maybe V) → K → Map K V → Map K V
update f = updateWithKey (λ _ v → f v)

updateLookupWithKey' : {K V : Set} → {{Comparable K}} → (K → V → Maybe V) → K → Map K V → StrictPair (Maybe V) (Map K V)
updateLookupWithKey' _ _ tip = nothing :*: tip
updateLookupWithKey' f k (node s k' v l r) with compare k k'
...                                        | lt with updateLookupWithKey' f k l
...                                             | found :*: l' = found :*: balanceR k' v l' r
updateLookupWithKey' f k (node s k' v l r) | gt with updateLookupWithKey' f k r
...                                             | found :*: r' = found :*: balanceL k' v l r'
updateLookupWithKey' f k (node s k' v l r) | eq with f k' v
...                                             | just v' = just v' :*: node s k' v' l r
...                                             | nothing = just v :*: glue l r
updateLookupWithKey : {K V : Set} → {{Comparable K}} → (K → V → Maybe V) → K → Map K V → Pair (Maybe V) (Map K V)
updateLookupWithKey f k m = toPair (updateLookupWithKey' f k m)

alter : {K V : Set} → {{Comparable K}} → (Maybe V → Maybe V) → K → Map K V → Map K V
alter f k tip with f nothing
...           | nothing = tip
...           | just v = singleton k v
alter f k (node s k' v l r) with compare k k'
...                         | lt = balance k' v (alter f k l) r
...                         | gt = balance k' v l (alter f k r)
...                         | eq with f (just v)
...                              | just v' = node s k' v' l r
...                              | nothing = glue l r

-- atKeyImpl : {K V : Set} → {{Functor F}} → {{Comparable K}} → AreWeStrict → K → (Maybe V → F (Maybe V)) → Map K V → F (Map K V)
-- atKeyImpl strict k f m with wordSize < 61 && size m >= alterFCutoff
-- ...                    | true = alterFFallback strict k f m
-- atKeyImpl strict k f m with lookupTract k m
-- ...                    | TraceResult mv q 

-- alterF : {K V : Set} → {{Functor F}} → {{Comparable K}} → (Maybe V → F (Maybe V)) → K → Map K V → F (Map K V)
-- alterF f k m = atKeyImpl Lazy k f m