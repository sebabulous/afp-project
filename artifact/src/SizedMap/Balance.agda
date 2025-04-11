module SizedMap.Balance where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import SizedMap.Query
open import SizedMap.Map
open import Helpers.Comparable
open import Helpers.Pair

private variable
  A B K V : Set
  m n p : Nat
  m1 n1 : Nat

data StrictPair (A B : Set): Set where
  _:*:_ : A → B → StrictPair A B

infixr 1 _:*:_

-- cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
-- cong f refl = refl

-- +zero : m + zero ≡ m
-- +zero {m = zero} = refl
-- +zero {m = suc m} = cong suc +zero

-- +suc : m + (suc n) ≡ suc (m + n)
-- +suc {m = zero} = refl
-- +suc {m = suc m} = cong suc +suc

-- {-# REWRITE +zero +suc #-}

-- +associative : m + (m1 + n1) ≡ m + m1 + n1
-- +associative {m = zero} = refl
-- +associative {m = suc m} = cong suc (+associative {m = m})

-- {-# REWRITE +zero +suc +associative #-}

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

{-# TERMINATING #-}
balance : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
balance k v tip tip = node k v tip tip

balance k v tip r@(node _ _ tip tip) = node k v tip r
balance k v tip r@(node rk rv tip rr@(node _ _ _ _)) = balance rk rv (node k v tip tip) rr
balance k v tip (node rk rv (node rlk rlv rll rlr) tip) = balance rlk rlv (node k v tip tip) (node rk rv rll rlr)
balance k v tip (node rk rv rl@(node rlk rlv rll rlr) rr@(node _ _ _ _)) with compare (size rl) (ratio * (size rr))
... | lt = node rk rv (node k v tip rl) rr
... | _ = node rlk rlv (node k v tip rll) (node rk rv rlr rr)

balance k v l@(node lk lv tip tip) tip = node k v l tip
balance k v (node lk lv tip (node lrk lrv lrl lrr)) tip = balance lrk lrv (node lk lv lrl lrr) (node k v tip tip)
balance k v (node lk lv ll@(node _ _ _ _) tip) tip = node lk lv ll (node k v tip tip)
balance k v (node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) tip with compare (size lr) (ratio * size ll)
balance k v (node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) tip | lt = node lk lv ll (node k v lr tip)
balance k v (node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) tip | gt = node lrk lrv (node lk lv ll lrl) (node k v lrr tip)
balance k v (node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) tip | eq = node lrk lrv (node lk lv ll lrl) (node k v lrr tip)

balance k v l@(node lk lv ll lr) r@(node rk rv rl rr) with (compare (size r) (delta * size l), compare (size l) (delta * size r))
balance k v l@(node lk lv ll lr) (node rk rv rl@(node rlk rlv rll rlr) rr@(node _ _ _ _)) | (gt,_) with (size rl) < ratio * (size rr)
balance k v l@(node lk lv ll lr) (node rk rv rl@(node rlk rlv rll rlr) rr@(node _ _ _ _)) | (gt,_) | true = node rk rv (node k v l rl) rr
balance k v l@(node lk lv ll lr) (node rk rv rl@(node rlk rlv rll rlr) rr@(node _ _ _ _)) | (gt,_) | false = node rlk rlv (node k v l rll) (node rk rv rlr rr)
balance k v l@(node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) r@(node rk rv rl rr) | (_,gt) with (size lr) < ratio * (size ll)
balance k v l@(node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) r@(node rk rv rl rr) | (_,gt) | true = node lk lv ll (node k v lr r)
balance k v l@(node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) r@(node rk rv rl rr) | (_,gt) | false = node lrk lrv (node lk lv ll lrl) (node k v lrr r)
balance k v l@(node lk lv _ _) r@(node rk rv rl rr) | _ = node k v l r


balanceL : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
balanceL k v tip tip = node k v tip tip

balanceL k v l@(node _ _ tip tip) tip = node k v l tip
balanceL k v (node lk lv tip (node lrk lrv _ _)) tip = {!   !}
balanceL k v (node lk lv ll@(node _ _ _ _) tip) tip = node lk lv ll (node k v tip tip)
balanceL k v (node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) tip with compare (size lr) (ratio * (size ll))
...                                                                                  | lt = node lk lv ll (node k v lr tip)
...                                                                                  | _ = node lrk lrv (node lk lv ll lrl) (node k v lrr tip)

balanceL k v tip r@(node _ _ _ _) = node k v tip r
balanceL k v l@(node lk lv ll lr) r@(node _ _ _ _) with compare (size r) (delta * size l)
balanceL k v (node lk lv ll@(node _ _ _ _) lr@(node lrk lrv lrl lrr)) r@(node _ _ _ _) | gt = if (size lr) < ratio * (size ll) then node lk lv ll (node k v lr r) else node lrk lrv (node lk lv ll lrl) (node k v lrr r)
balanceL k v l@(node lk lv ll lr) r@(node _ _ _ _) | _ = node k v l r


balanceR : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
balanceR k v tip tip = node k v tip tip

balanceR k v tip r@(node _ _ tip tip) = node k v tip r
balanceR k v tip (node rk rv tip rr@(node _ _ _ _)) = node rk rv (node k v tip tip) rr
balanceR k v tip (node rk rv (node rlk rlv _ _) tip) = {!   !}
balanceR k v tip (node rk rv rl@(node rlk rlv rll rlr) rr@(node _ _ _ _)) with (size rl) < ratio * (size rr)
...                                                                                  | true = node rk rv (node k v tip rl) rr
...                                                                                  | false = node rlk rlv (node k v tip rll) (node rk rv rlr rr)

balanceR k v l@(node _ _ _ _) tip = node k v l tip
balanceR k v l@(node _ _ _ _) r@(node _ _ _ _) with compare (size r) (delta * size l)
balanceR k v l@(node _ _ _ _) (node rk rv rl@(node rlk rlv rll rlr) rr@(node _ _ _ _)) | gt = if (size rl) < ratio * (size rr) then node rk rv (node k v l rl) rr else node rlk rlv (node k v l rll) (node rk rv rlr rr)
balanceR k v l@(node _ _ _ _) r@(node _ _ _ _) | _ = node k v l r

data MinView (K : Set) (V : Set) : Nat → Set where
  minview : K → V → Map K V n → MinView K V n

data MaxView (K : Set) (V : Set) : Nat → Set where
  maxview : K → V → Map K V n → MaxView K V n

minViewSure : {{Comparable K}} → K → V → Map K V m → Map K V n → MinView K V (m + n)
minViewSure k v tip r = minview k v r
minViewSure k v (node kl vl ll lr) r with minViewSure kl vl ll lr
...                                    | minview km vm l' = minview km vm (balanceR k v l' r)

maxViewSure : {{Comparable K}} → K → V → Map K V m → Map K V n → MaxView K V (m + n)
maxViewSure k v l tip = maxview k v l
maxViewSure k v l (node kr vr rl rr) with maxViewSure kr vr rl rr
...                                    | maxview km vm r' = maxview km vm (balanceL k v l r')

glue : {{Comparable K}} → Map K V m → Map K V n → Map K V (m + n)
glue tip r = r
glue l tip = l
glue l@(node kl vl ll lr) r@(node kr vr rl rr) with compare (size l) (size r)
...                                                  | gt with maxViewSure kl vl ll lr
...                                                       | maxview km m l' = balanceR km m l' r
glue l@(node kl vl ll lr) r@(node kr vr rl rr) | _  with minViewSure kr vr rl rr
...                                                       | minview km m r' = balanceL km m l r'



insertMin : {{Comparable K}} → K → V → Map K V n → Map K V (suc n)
insertMin k v tip = node k v tip tip
insertMin k v (node k' v' l r) = balanceL k' v' (insertMin k v l) r

insertMax : {{Comparable K}} → K → V → Map K V n → Map K V (suc n)
insertMax k v tip = node k v tip tip
insertMax k v (node k' v' l r) = balanceR k' v' l (insertMax k v r)

link : {{Comparable K}} → K → V → Map K V m → Map K V n → Map K V (suc (m + n))
link kx x tip r = insertMin kx x r
link kx x l tip = insertMax kx x l
link kx x l@(node ky y ly ry) r@(node kz z lz rz) with (compare (delta * size l) (size r) , compare (delta * (size r)) (size l))
...                                                           | (_ , lt) = balanceR ky y ly (link kx x ry r)
...                                                           | _ = node kx x l r

link2 : {{Comparable K}} → Map K V m → Map K V n → Map K V (m + n)
link2 tip r = r
link2 l tip = l
link2 l@(node kx x lx rx) r@(node ky y ly ry) with (compare (delta * (size l)) (size r) , compare (delta * (size r)) (size l))
...                                                       | (_ , lt) = balanceR kx x lx (link2 rx r)
...                                                       | (_ , _) = glue l r 