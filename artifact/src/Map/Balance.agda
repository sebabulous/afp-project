module Map.Balance where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Map.Query
open import Map.Construction
open import Map.Map

private variable
  A B K V : Set
  m n p : Nat
  m1 n1 : Nat

data StrictPair (A B : Set): Set where
  _:*:_ : A → B → StrictPair A B

infixr 1 _:*:_

cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

+zero : m + zero ≡ m
+zero {m = zero} = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero} = refl
+suc {m = suc m} = cong suc +suc

+associative : m + (m1 + n1) ≡ m + m1 + n1
+associative {m = zero} = refl
+associative {m = suc m} = cong suc (+associative {m = m})

{-# REWRITE +zero +suc +associative #-}

fst : StrictPair A B → A
fst (a :*: _) = a

snd : StrictPair A B → B
snd (_ :*: b) = b

toPair : StrictPair A B → Pair A B
toPair (a :*: b) = (a , b)


if_then_else_ : Bool → A → A → A
if_then_else_ true a _ = a
if_then_else_ false _ a = a

delta = 3
ratio = 2

-- balance' : K → A → Map K A m → Map K A n → Map K A (suc (m + n))
-- balance' k a tip tip = node 1 k a tip tip
-- balance' k a tip r@(node _ _ _ tip tip) = node 2 k a tip r
-- balance' k a l@(node _ _ _ tip tip) tip = node 2 k a l tip
-- balance' k a tip r = {! rotateL k a tip r  !} -- sizeR > delta * sizeL (sizeR > 3 ∙ 0)
-- balance' k a l tip = {! rotateR k a l tip  !} -- sizeL > delta * sizeR (sizeL > 3 ∙ 0)
-- balance' k a l@(node ls lk lv ll lr) r@(node rs rk rv rl rr) with (compare (size r) (delta * size l) , compare (size l) (delta * size r))
-- ...                                                          | (gt , _) with compare (size rl) (ratio * size rr)
-- ...                                                                     | lt = node (size l + size rl + size rr + 2) rk rv (node (size l + size rl + 1) k a l rl) rr
-- ...                                                                     | _ = {!   !}
-- balance' k a l@(node ls lk lv ll lr) r@(node rs rk rv rl rr) | (_ , gt) with compare (size lr) (ratio * size ll)
-- -- ...                                                                     | lt = node (size ll + size lr + size r + 1) lk lv ll (node (size lr + size r + 1) k a lr r)
-- ...                                                                     | lt = {!   !}
-- ...                                                                     | _ = {! doubleR k a l r !}
-- balance' k a l@(node ls lk lv ll lr) r@(node rs rk rv rl rr) | (_ , _) = node (size l + size r + 1) k a l r




balance : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
balance k v tip tip = node 1 k v tip tip

balance k v tip r@(node _ _ _ tip tip) = node 2 k v tip r
balance k v tip r@(node _ rk rv tip rr@(node _ _ _ _ _)) = node 3 rk rv (node 1 k v tip tip) rr
-- balance k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = node 3 rlk rlv (node 1 k v tip tip) (node 1 rk rv tip tip)
balance k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = {! This does not make sense  !}
balance k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) with compare rls (ratio * rrs)
...                                                                                 | lt = node (1 + rs) rk rv (node (1 + rls) k v tip rl) rr
...                                                                                 | _ = node (1 + rs) rlk rlv (node (1 + size rll) k v tip rll) (node (1 + rrs + size rlr) rk rv rlr rr)

balance k v l@(node ls lk lv tip tip) tip = node 2 k v l tip
-- balance k v (node ls lk lv tip (node _ lrk lrv _ _)) tip = node 3 lrk lrv (node 1 lk lv tip tip) (node 1 k v tip tip)
balance k v (node ls lk lv tip (node _ lrk lrv _ _)) tip = {!   !}
balance k v (node ls lk lv ll@(node _ _ _ _ _) tip) tip = node 3 lk lv ll (node 1 k v tip tip)
balance k v (node ls lk lv (node lls _ _ _ _) (node lrs lrk lrv lrl lrr)) tip with compare lrs (ratio * lls)
balance k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) tip | lt = node (1 + ls) lk lv ll (node (1 + lrs) k v lr tip)
balance k v (node ls lk lv ll@(node lls _ _ _ _) (node lrs lrk lrv lrl lrr)) tip | _ = node (1 + ls) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + size lrr) k v lrr tip)

balance k v (node ls lk lv ll lr) (node rs rk rv rl rr) with (compare rs (delta * ls), compare ls (delta * rs))
balance k v l@(node ls lk lv ll lr) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | (gt,_) = if rls < ratio * rrs then node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr else node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
balance k v l@(node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs rk rv rl rr) | (_,gt) = if lrs < ratio * lls then node (1 + ls + rs) lk lv ll (node (1 + rs + lrs) k v lr r) else node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
balance k v l@(node ls lk lv _ _) r@(node rs rk rv rl rr) | _ = node (1 + ls + rs) k v l r




balanceL : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
balanceL k v tip tip = node 1 k v tip tip

balanceL k v l@(node _ _ _ tip tip) tip = node 2 k v l tip
-- balanceL k v (node _ lk lv tip (node _ lrk lrv _ _)) tip = node 3 lrk lrv (node 1 lk lv tip tip) (node 1 k v tip tip)
balanceL k v (node _ lk lv tip (node _ lrk lrv _ _)) tip = {!   !}
balanceL k v (node _ lk lv ll@(node _ _ _ _ _) tip) tip = node 3 lk lv ll (node 1 k v tip tip)
balanceL k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) tip with compare lrs (ratio * lls)
...                                                                                  | lt = node (1 + ls) lk lv ll (node (1 + lrs) k v lr tip)
...                                                                                  | _ = node (1 + ls) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + size lrr) k v lrr tip)

balanceL k v tip r@(node rs _ _ _ _) = node (1 + rs) k v tip r
balanceL k v (node ls lk lv ll lr) (node rs _ _ _ _) with compare rs (delta * ls)
balanceL k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs _ _ _ _) | gt = if lrs < ratio * lls then node (1 + ls + rs) lk lv ll (node (1 + rs + lrs) k v lr r) else node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
balanceL k v l@(node ls lk lv ll lr) r@(node rs _ _ _ _) | _ = node (1 + ls + rs) k v l r


balanceR : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
balanceR k v tip tip = node 1 k v tip tip

balanceR k v tip r@(node _ _ _ tip tip) = node 2 k v tip r
balanceR k v tip (node _ rk rv tip rr@(node _ _ _ _ _)) = node 3 rk rv (node 1 k v tip tip) rr
-- balanceR k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = node 3 rlk rlv (node 1 k v tip tip) (node 1 rk rv tip tip)
balanceR k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = {!   !}
balanceR k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) with rls < ratio * rrs
...                                                                                  | true = node (1 + rs) rk rv (node (1 + rls) k v tip rl) rr
...                                                                                  | false = node (1 + rs) rlk rlv (node (1 + size rll) k v tip rll) (node (1 + rrs + size rlr) rk rv rlr rr)

balanceR k v l@(node ls _ _ _ _) tip = node (1 + ls) k v l tip
balanceR k v (node ls _ _ _ _) (node rs _ _ _ _) with compare rs (delta * ls)
balanceR k v l@(node ls _ _ _ _) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | gt = if rls < ratio * rrs then node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr else node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
balanceR k v l@(node ls _ _ _ _) r@(node rs _ _ _ _) | _ = node (1 + ls + rs) k v l r

data MinView (K : Set) (V : Set) : Nat → Set where
  minview : K → V → Map K V n → MinView K V n
-- record MinView (K : Set) (V : Set) : Set where
--   field
--     minK : K
--     minV : V
--     minM : Map K V n

data MaxView (K : Set) (V : Set) : Nat → Set where
  maxview : K → V → Map K V n → MaxView K V n
-- record MaxView (K : Set) (V : Set) : Set where
--   field
--     maxK : K
--     maxV : V
--     maxM : Map K V n

minViewSure : {{Comparable K}} → K → V → Map K V m → Map K V n → MinView K V (m + n)
minViewSure k v tip r = minview k v r
minViewSure k v (node _ kl vl ll lr) r with minViewSure kl vl ll lr
...                                    | minview km vm l' = minview km vm (balanceR k v l' r)
-- minViewSure : {{Comparable K}} → K → V → Map K V m → Map K V n → MinView K V
-- minViewSure k v tip r = record {minK = k ; minV = v ; minM = r}
-- minViewSure k v (node _ kl vl ll lr) r with minViewSure kl vl ll lr
-- ...                                    | record {minK = km ; minV = vm ; minM = l'} = record {minK = km ; minV = vm ; minM = balanceR k v l' r}

maxViewSure : {{Comparable K}} → K → V → Map K V m → Map K V n → MaxView K V (m + n)
maxViewSure k v l tip = maxview k v l
maxViewSure k v l (node _ kr vr rl rr) with maxViewSure kr vr rl rr
...                                    | maxview km vm r' = maxview km vm (balanceL k v l r')
-- maxViewSure : {{Comparable K}} → K → V → Map K V → Map K V → MaxView K V
-- maxViewSure k v l tip = record {maxK = k ; maxV = v ; maxM = l}
-- maxViewSure k v l (node _ kr vr rl rr) with maxViewSure kr vr rl rr
-- ...                                    | record {maxK = km ; maxV = vm ; maxM = r'} = record {maxK = km ; maxV = vm ; maxM = balanceL k v l r'}

glue : {{Comparable K}} → Map K V m → Map K V n → Map K V (m + n)
glue tip r = r
glue l tip = l
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) with compare sl sr
...                                                  | gt with maxViewSure kl vl ll lr
...                                                       | maxview km m l' = balanceR km m l' r
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | _  with minViewSure kr vr rl rr
...                                                       | minview km m r' = balanceL km m l r'
-- glue : {{Comparable K}} → Map K V → Map K V → Map K V
-- glue tip r = r
-- glue l tip = l
-- glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) with compare sl sr
-- ...                                                  | gt = let record {maxK = km ; maxV = m ; maxM = l'} = maxViewSure kl vl ll lr in balanceR km m l' r
-- ...                                                  | _ = let record {minK = km ; minV = m ; minM = r'} = minViewSure kr vr rl rr in balanceL km m l r'



insertMin : {{Comparable K}} → K → V → Map K V n → Map K V (suc n)
insertMin k v tip = singleton k v
insertMin k v (node _ k' v' l r) = balanceL k' v' (insertMin k v l) r
-- insertMin : {{Comparable K}} → K → V → Map K V → Map K V
-- insertMin k v tip = singleton k v
-- insertMin k v (node _ k' v' l r) = balanceL k' v' (insertMin k v l) r

insertMax : {{Comparable K}} → K → V → Map K V n → Map K V (suc n)
insertMax k v tip = singleton k v
insertMax k v (node _ k' v' l r) = balanceR k' v' l (insertMax k v r)
-- insertMax : {{Comparable K}} → K → V → Map K V → Map K V
-- insertMax k v tip = singleton k v
-- insertMax k v (node _ k' v' l r) = balanceR k' v' l (insertMax k v r)

link : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
link kx x tip r = insertMin kx x r
link kx x l tip = insertMax kx x l
link kx x l@(node sizeL ky y ly ry) r@(node sizeR kz z lz rz) with (compare (delta * sizeL) sizeR , compare (delta * sizeR) sizeL)
-- ...                                                           | (lt , _) = balanceL kz z (link kx x l lz) rz
...                                                           | (_ , lt) = balanceR ky y ly (link kx x ry r)
...                                                           | _ = node (size l + size r + 1) kx x l r
-- link : {{Comparable K}} → K → V → Map K V → Map K V → Map K V
-- link kx x tip r = insertMin kx x r
-- link kx x l tip = insertMax kx x l
-- link kx x l@(node sizeL ky y ly ry) r@(node sizeR kz z lz rz) with (compare (delta * sizeL) sizeR , compare (delta * sizeR) sizeL)
-- -- ...                                                           | (lt , _) = balanceL kz z (link kx x l lz) rz
-- ...                                                           | (_ , lt) = balanceR ky y ly (link kx x ry r)
-- ...                                                           | (_ , _) = node (size l + size r + 1) kx x l r

link2 : {{Comparable K}} → Map K V m → Map K V n → Map K V (m + n)
link2 tip r = r
link2 l tip = l
link2 l@(node sizeL kx x lx rx) r@(node sizeR ky y ly ry) with (compare (delta * sizeL) sizeR , compare (delta * sizeR) sizeL)
-- ...                                                       | (lt , _) = balanceL ky y (link2 l ly) ry
...                                                       | (_ , lt) = balanceR kx x lx (link2 rx r)
...                                                       | (_ , _) = glue l r 
-- link2 : {{Comparable K}} → Map K V → Map K V → Map K V
-- link2 tip r = r
-- link2 l tip = l
-- link2 l@(node sizeL kx x lx rx) r@(node sizeR ky y ly ry) with (compare (delta * sizeL) sizeR , compare (delta * sizeR) sizeL)
-- -- ...                                                       | (lt , _) = balanceL ky y (link2 l ly) ry
-- ...                                                       | (_ , lt) = balanceR kx x lx (link2 rx r)
-- ...                                                       | (_ , _) = glue l r 