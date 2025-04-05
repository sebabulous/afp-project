module Map.Balance where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

open import Map.Query
open import Map.Construction
open import Map.Map

private variable
  K V A : Set

data StrictPair (A B : Set): Set where
  _:*:_ : A → B → StrictPair A B

infixr 1 _:*:_

fst : {A B : Set} → StrictPair A B → A
fst (a :*: _) = a

snd : {A B : Set} → StrictPair A B → B
snd (_ :*: b) = b

toPair : {A B : Set} → StrictPair A B → Pair A B
toPair (a :*: b) = (a , b)


if_then_else_ : {A : Set} → Bool → A → A → A
if_then_else_ true a _ = a
if_then_else_ false _ a = a

delta = 3
ratio = 2

balance' : K → A → Map K A → Map K A → Map K A
balance' k a tip tip = node 1 k a tip tip
balance' k a tip r@(node rs rk ra tip tip) = node 2 k a tip r
balance' k a tip r@(node rs rk ra tip rr@(node _ _ _ _ _)) = node 2 rk ra (node 1 k a tip tip) rr
balance' k a tip r@(node rs rk ra rl@(node _ rlk rla _ _) tip)  = node 3 rlk rla (node 1 k a tip tip) (node 1 rk ra tip tip)
balance' k a tip r@(node rs rk ra rl@(node rls rlk rla _ _) rr@(node rrs _ _ _ _)) with compare rls (ratio * rrs)
balance' k a tip r@(node rs rk ra rl@(node rls rlk rla _ _) rr@(node rrs _ _ _ _)) | lt = node (1 + rs) rk ra (node (1 + rls) k a tip rl) rr
balance' k a tip r@(node rs rk ra rl@(node _ rlk rla rll rlr) rr@(node rrs _ _ _ _)) | gt = node (1 + rs) rlk rla (node (1 + size rll) k a tip rll) (node (1 + rrs + size rlr) rk ra rlr rr)
balance' k a tip r@(node rs rk ra rl@(node _ rlk rla rll rlr) rr@(node rrs _ _ _ _)) | eq = node (1 + rs) rlk rla (node (1 + size rll) k a tip rll) (node (1 + rrs + size rlr) rk ra rlr rr)
balance' k a l@(node ls lk la tip tip) tip = node 2 k a l tip
balance' k a l@(node ls lk la tip (node lrs lrk lra lrl lrr)) tip = node 3 lrk lra (node 1 lk la tip tip) (node 1 k a tip tip)
balance' k a l@(node ls lk la ll@(node lls llk lla lll llr) tip) tip = node 3 lk la ll (node 1 k a tip tip)
balance' k a l@(node ls lk la ll@(node lls llk lla lll llr) lr@(node lrs lrk lra lrl lrr)) tip with compare lrs (ratio * lls)
balance' k a l@(node ls lk la ll@(node lls llk lla lll llr) lr@(node lrs lrk lra lrl lrr)) tip | lt = node (1 + ls) lk la ll (node (1 + lrs) k a lr tip)
balance' k a l@(node ls lk la ll@(node lls llk lla lll llr) lr@(node lrs lrk lra lrl lrr)) tip | gt = node (1 + ls) lrk lra (node (1 + lls + size lrl) lk la ll lrl) (node (1 + size lrr) k a lrr tip)
balance' k a l@(node ls lk la ll@(node lls llk lla lll llr) lr@(node lrs lrk lra lrl lrr)) tip | eq = node (1 + ls) lrk lra (node (1 + lls + size lrl) lk la ll lrl) (node (1 + size lrr) k a lrr tip)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) with compare rs (delta * ls)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | gt with (rl , rr)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | gt | (node rls rlk rla rll rlr , node rrs rrk rra rrl rrr) with compare rls (ratio * rrs)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | gt | (node rls rlk rla rll rlr , node rrs rrk rra rrl rrr) | lt = node (1 + ls + rs) rk ra (node (1 + ls + rls) k a l rl) rr
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | gt | (node rls rlk rla rll rlr , node rrs rrk rra rrl rrr) | _ = node (1 + ls + rs) rlk rla (node (1 + ls + size rll) k a l rll) (node (1 + rrs + size rlr) rk ra rlr rr)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | gt | _ = {! ERROR !}
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | _ with (ll , lr)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | _ | (node lls llk lla lll llr , node lrs lrk lra lrl lrr) with compare lrs (ratio * lls)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | _ | (node lls llk lla lll llr , node lrs lrk lra lrl lrr) | lt = node (1 + ls + rs) lk la ll (node (1 + rs + lrs) k a lr r)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | _ | (node lls llk lla lll llr , node lrs lrk lra lrl lrr) | _ = node (1 + ls + rs) lrk lra (node (1 + lls + size lrl) lk la ll lrl) (node (1 + rs + size lrr) k a lrr r)
balance' k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) | _ | _ = {! ERROR !}


balance : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
balance k a l@(node ls _ _ _ _) r@(node rs _ _ _ _) with (compare rs (delta * ls) , compare ls (delta * rs))
balance k a l@(node ls _ _ _ _) r@(node rs _ _ _ _) | (gt , _) = balance' k a l r
balance k a l@(node ls _ _ _ _) r@(node rs _ _ _ _) | (_ , gt) = balance' k a l r
balance k a l@(node ls _ _ _ _) r@(node rs _ _ _ _) | _ = node (1 + ls + rs) k a l r
balance k a l r = balance' k a l r

-- balance : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
-- balance k v tip tip = node 1 k v tip tip

-- balance k v tip r@(node _ _ _ tip tip) = node 2 k v tip r
-- balance k v tip r@(node _ rk rv tip rr@(node _ _ _ _ _)) = node 3 rk rv (node 1 k v tip tip) rr
-- balance k v tip (node _ rk rv (node _ rlk rlv _ _) tip) = node 3 rlk rlv (node 1 k v tip tip) (node 1 rk rv tip tip)
-- balance k v tip (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) with compare rls (ratio * rrs)
-- ... | lt = node (1 + rs) rk rv (node (1 + rls) k v tip rl) rr
-- ... | gt = node (1 + rs) rlk rlv (node (1 + size rll) k v tip rll) (node (1 + rrs + size rlr) rk rv rlr rr)
-- ... | eq = node (1 + rs) rlk rlv (node (1 + size rll) k v tip rll) (node (1 + rrs + size rlr) rk rv rlr rr)

-- balance k v l@(node ls lk lv tip tip) tip = node 2 k v l tip
-- balance k v (node ls lk lv tip (node _ lrk lrv _ _)) tip = node 3 lrk lrv (node 1 lk lv tip tip) (node 1 k v tip tip)
-- balance k v (node ls lk lv ll@(node _ _ _ _ _) tip) tip = node 3 lk lv ll (node 1 k v tip tip)
-- balance k v (node ls lk lv (node lls _ _ _ _) (node lrs lrk lrv lrl lrr)) tip with compare lrs (ratio * lls)
-- balance k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) tip | lt = node (1 + ls) lk lv ll (node (1 + lrs) k v lr tip)
-- balance k v (node ls lk lv ll@(node lls _ _ _ _) (node lrs lrk lrv lrl lrr)) tip | _ = node (1 + ls) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + size lrr) k v lrr tip)

-- balance k v (node ls lk lv ll lr) (node rs rk rv rl rr) with (compare rs (delta * ls), compare ls (delta * rs))
-- balance k v l@(node ls lk lv ll lr) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | (gt,_) with compare rls (ratio * rrs)
-- balance k v l@(node ls lk lv ll lr) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | (gt,_) | lt = node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr
-- balance k v l@(node ls lk lv ll lr) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | (gt,_) | gt = node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
-- balance k v l@(node ls lk lv ll lr) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | (gt,_) | eq = node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
-- balance k v l@(node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs rk rv rl rr) | (_,gt) with compare lrs (ratio * lls)
-- balance k v l@(node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs rk rv rl rr) | (_,gt) | lt = node (1 + ls + rs) lk lv ll (node (1 + rs + lrs) k v lr r)
-- balance k v l@(node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs rk rv rl rr) | (_,gt) | gt = node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
-- balance k v l@(node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs rk rv rl rr) | (_,gt) | eq = node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
-- balance k v l@(node ls lk lv _ _) r@(node rs rk rv rl rr) | _ = node (1 + ls + rs) k v l r




balanceL : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
balanceL k v tip tip = node 1 k v tip tip

balanceL k v l@(node _ _ _ tip tip) tip = node 2 k v l tip
balanceL k v (node _ lk lv tip (node _ lrk lrv _ _)) tip = node 3 lrk lrv (node 1 lk lv tip tip) (node 1 k v tip tip)
balanceL k v (node _ lk lv ll@(node _ _ _ _ _) tip) tip = node 3 lk lv ll (node 1 k v tip tip)
balanceL k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) tip with compare lrs (ratio * lls)
... | lt = node (1 + ls) lk lv ll (node (1 + lrs) k v lr tip)
... | _ = node (1 + ls) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + size lrr) k v lrr tip)

balanceL k v tip r@(node rs _ _ _ _) = node (1 + rs) k v tip r
balanceL k v (node ls lk lv ll lr) (node rs _ _ _ _) with compare rs (delta * ls)
balanceL k v (node ls lk lv ll@(node lls _ _ _ _) lr@(node lrs lrk lrv lrl lrr)) r@(node rs _ _ _ _) | gt with compare lrs (ratio * lls)
... | lt = node (1 + ls + rs) lk lv ll (node (1 + rs + lrs) k v lr r)
... | eq = node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
... | gt = node (1 + ls + rs) lrk lrv (node (1 + lls + size lrl) lk lv ll lrl) (node (1 + rs + size lrr) k v lrr r)
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
-- balanceR k v l@(node ls _ _ _ _) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | gt = if rls < ratio * rrs then node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr else node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
balanceR k v l@(node ls _ _ _ _) (node rs rk rv rl@(node rls rlk rlv rll rlr) rr@(node rrs _ _ _ _)) | gt with compare rls (ratio * rrs)
... | lt = node (1 + ls + rs) rk rv (node (1 + ls + rls) k v l rl) rr
... | eq = node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
... | gt = node (1 + ls + rs) rlk rlv (node (1 + ls + size rll) k v l rll) (node (1 + rrs + size rlr) rk rv rlr rr)
-- balanceR k v l@(node ls _ _ _ _) r@(node rs _ _ _ _) | _ = node (1 + ls + rs) k v l r
balanceR k v l@(node ls _ _ _ _) r@(node rs _ _ _ _) | lt = node (1 + ls + rs) k v l r
balanceR k v l@(node ls _ _ _ _) r@(node rs _ _ _ _) | eq = node (1 + ls + rs) k v l r
balanceR k v l@(node ls _ _ _ _) r@(node rs _ _ _ _) | gt = node (1 + ls + rs) k v l r

data MinView (K : Set) (V : Set) : Set where
  minview : K → V → Map K V → MinView K V

-- record MinView (K : Set) (V : Set): Set where
--   field
--     minK : K
--     minV : V
--     minM : Map K V

data MaxView (K : Set) (V : Set) : Set where
  maxview : K → V → Map K V → MaxView K V
  
-- record MaxView (K : Set) (V : Set): Set where
--   field
--     maxK : K
--     maxV : V
--     maxM : Map K V

minViewSure : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → MinView K V
minViewSure k v tip r = minview k v r
minViewSure k v (node _ kl vl ll lr) r with minViewSure kl vl ll lr
...                                    | minview km vm l' = minview km vm (balanceR k v l' r)
-- minViewSure : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → MinView K V
-- minViewSure k v tip r = record {minK = k ; minV = v ; minM = r}
-- minViewSure k v (node _ kl vl ll lr) r with minViewSure kl vl ll lr
-- ...                                    | record {minK = km ; minV = vm ; minM = l'} = record {minK = km ; minV = vm ; minM = balanceR k v l' r}

maxViewSure : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → MaxView K V
maxViewSure k v l tip = maxview k v l
maxViewSure k v l (node _ kr vr rl rr) with maxViewSure kr vr rl rr
...                                    | maxview km vm r' = maxview km vm (balanceL k v l r')
-- maxViewSure : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → MaxView K V
-- maxViewSure k v l tip = record {maxK = k ; maxV = v ; maxM = l}
-- maxViewSure k v l (node _ kr vr rl rr) with maxViewSure kr vr rl rr
-- ...                                    | record {maxK = km ; maxV = vm ; maxM = r'} = record {maxK = km ; maxV = vm ; maxM = balanceL k v l r'}

glue : {K V : Set} → {{Comparable K}} → Map K V → Map K V → Map K V
glue tip r = r
glue l@(node _ _ _ _ _) tip = l
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) with compare sl sr
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | gt with maxViewSure kl vl ll lr
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | gt | maxview km m l' = balanceR km m l' r
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | eq with minViewSure kr vr rl rr
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | eq | minview km m r' = balanceL km m l r'
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | lt with minViewSure kr vr rl rr
glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) | lt | minview km m r' = balanceL km m l r'
-- glue : {K V : Set} → {{Comparable K}} → Map K V → Map K V → Map K V
-- glue tip r = r
-- glue l@(node _ _ _ _ _) tip = l
-- glue l@(node sl kl vl ll lr) r@(node sr kr vr rl rr) with compare sl sr
-- ...                                                  | gt = let record {maxK = km ; maxV = m ; maxM = l'} = maxViewSure kl vl ll lr in balanceR km m l' r
-- ...                                                  | eq = let record {minK = km ; minV = m ; minM = r'} = minViewSure kr vr rl rr in balanceL km m l r'
-- ...                                                  | lt = let record {minK = km ; minV = m ; minM = r'} = minViewSure kr vr rl rr in balanceL km m l r'



insertMin : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V
insertMin k v tip = singleton k v
insertMin k v (node _ k' v' l r) = balanceL k' v' (insertMin k v l) r

insertMax : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V
insertMax k v tip = singleton k v
insertMax k v (node _ k' v' l r) = balanceR k' v' l (insertMax k v r)

{-# TERMINATING #-}
link : {K V : Set} → {{Comparable K}} → K → V → Map K V → Map K V → Map K V
link k a tip r = insertMin k a r
link k a l tip = insertMax k a l
link k a l@(node ls lk la ll lr) r@(node rs rk ra rl rr) with (compare (delta * ls) rs , compare (delta * rs) ls)
... | (lt , _) = balanceL rk ra (link k a l rl) rr
... | (_ , lt) = balanceR lk la ll (link k a lr r)
... | _ = node (size l + size r + 1) k a l r

{-# TERMINATING #-}
link2 : {K V : Set} → {{Comparable K}} → Map K V → Map K V → Map K V
link2 tip r = r
link2 l tip = l
link2 l@(node ls lk la ll lr) r@(node rs rk ra rl rr) with (compare (delta * ls) rs , compare (delta * rs) ls)
...                                                       | (lt , _) = balanceL rk ra (link2 l rl) rr
...                                                       | (_ , lt) = balanceR lk la ll (link2 lr r)
...                                                       | _ = glue l r

insertR : {{Comparable K}} → K → A → Map K A → Map K A
insertR k a m = go k k a m
  where
    go : {{Comparable K}} → K → K → A → Map K A → Map K A
    go orig _ a' tip = node 1 orig a' tip tip
    go orig k' a' t@(node _ k a l r) with compare k' k
    ... | lt = balanceL k a (go orig k' a' l) r
    ... | gt = balanceR k a l (go orig k' a' r)
    ... | eq = t

insertWithR : {{Comparable K}} → (A → A → A) → K → A → Map K A → Map K A
insertWithR _ k a tip = node 1 k a tip tip
insertWithR f k' a' (node s k a l r) with compare k' k
insertWithR f k' a' (node s k a l r) | lt = balanceL k a (insertWithR f k' a' l) r
insertWithR f k' a' (node s k a l r) | gt = balanceR k a l (insertWithR f k' a' r)
insertWithR f k' a' (node s k a l r) | eq = node s k (f a a') l r