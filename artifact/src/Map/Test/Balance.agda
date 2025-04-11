module Map.Test.Balance where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

open import Map.Map
open import Map.Balance
open import Map.Test.Valid
open import Map.Test.Cases
open import Map.Test.Balance.BalanceL
open import Map.Test.Balance.BalanceR
open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A : Set

balanceRetainsElementsL : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {ml mr : Map K A} → (k , a) ∈ ml → (k , a) ∈ balance k' a' ml mr
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la tip tip} {tip} prf = thereL prf
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la tip (node lrs lrk lra lrl lrr)} {tip} here = thereL here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la tip (node lrs lrk lra lrl lrr)} {tip} (thereR here) = here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la tip (node lrs lrk lra lrl lrr)} {tip} (thereR (thereL prf)) = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la tip (node lrs lrk lra lrl lrr)} {tip} (thereR (thereR prf)) = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) tip} {tip} here = here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) tip} {tip} (thereL prf) = thereL prf
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} here with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} here | lt = here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} here | gt = thereL here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} here | eq = thereL here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereL prf) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereL prf) | lt = thereL prf
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereL prf) | gt = thereL (thereL prf)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereL prf) | eq = thereL (thereL prf)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR here) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR here) | lt = thereR (thereL here)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR here) | gt = here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR here) | eq = here
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereL prf)) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereL prf)) | lt = thereR (thereL (thereL prf))
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereL prf)) | gt = thereL (thereR prf)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereL prf)) | eq = thereL (thereR prf)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereR prf)) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereR prf)) | lt = thereR (thereL (thereR prf))
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereR prf)) | gt = thereR (thereL prf)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la (node lls llk lla lll llr) (node lrs lrk lra lrl lrr)} {tip} (thereR (thereR prf)) | eq = thereR (thereL prf)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here with compare rs (delta * ls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | gt with (rl , rr)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) with compare rls (ratio * rrs)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) | lt = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) | _ = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | gt | _ = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | _ with (ll , lr)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) | lt = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) | _ = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} here | _ | _ = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) with compare rs (delta * ls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | gt with (rl , rr)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) with compare rls (ratio * rrs)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) | lt = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) | _ = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | gt | _ = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | _ with (ll , lr)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) | lt = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) | _ = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | _ | _ = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) with compare rs (delta * ls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | gt with (rl , rr)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) with compare rls (ratio * rrs)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) | lt = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | gt | (node rls rlk rla rll rlr , node rrs _ _ _ _) | _ = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | gt | _ = {! ERROR !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | _ with (ll , lr)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) with compare lrs (ratio * lls)
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) | lt = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | _ | (node lls _ _ _ _ , node lrs lrk lra lrl lrr) | _ = {!   !}
balanceRetainsElementsL {K} {A} ⦃ x ⦄ {k} {k'} {a} {a'} {node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | _ | _ = {! ERROR !}



insertMinRetainsElementsHere : {{_ : Comparable K}} → {k : K} → {a : A} → {m : Map K A} → (k , a) ∈ insertMin k a m
insertMinRetainsElementsHere {m = tip} = here
insertMinRetainsElementsHere {m = node _ k' a' l r} = balanceLRetainsElementsL {_} {_} {_} {k'} {_} {a'} {_} {r} (insertMinRetainsElementsHere {_} {_} {_} {_} {l})

insertMinRetainsElementsThere : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {m : Map K A} → (k , a) ∈ m → (k , a) ∈ insertMin k' a' m
insertMinRetainsElementsThere {k = k} {k'} {a} {a'} {node _ mk ma l r} here = balanceLRetainsElementsHere {_} {_} {_} {_} {insertMin k' a' l} {r}
insertMinRetainsElementsThere {k = k} {k'} {a} {a'} {node _ mk ma l r} (thereL prf) = balanceLRetainsElementsL {_} {_} {_} {mk} {_} {ma} {_} {r} (insertMinRetainsElementsThere {_} {_} {_} {k'} {_} {a'} {l} prf)
insertMinRetainsElementsThere {k = k} {k'} {a} {a'} {node _ mk ma l r} (thereR prf) = balanceLRetainsElementsR {_} {_} {_} {mk} {_} {ma} {insertMin k' a' l} {r} prf


insertMaxRetainsElementsHere : {{_ : Comparable K}} → {k : K} → {a : A} → {m : Map K A} → (k , a) ∈ insertMax k a m
insertMaxRetainsElementsHere {m = tip} = here
insertMaxRetainsElementsHere {k = k} {a} {node _ k' a' l r} = balanceRRetainsElementsR {_} {_} {_} {k'} {_} {a'} {l} {insertMax k a r} (insertMaxRetainsElementsHere {_} {_} {_} {_} {r})

insertMaxRetainsElementsThere : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {m : Map K A} → (k , a) ∈ m → (k , a) ∈ insertMax k' a' m
insertMaxRetainsElementsThere {k = k} {k'} {a} {a'} {node _ mk ma l r} here = balanceRRetainsElementsHere {_} {_} {_} {_} {l} {insertMax k' a' r}
insertMaxRetainsElementsThere {k = k} {k'} {a} {a'} {node _ mk ma l r} (thereL prf) = balanceRRetainsElementsL prf
insertMaxRetainsElementsThere {k = k} {k'} {a} {a'} {node _ mk ma l r} (thereR prf) = balanceRRetainsElementsR {_} {_} {_} {mk} {_} {ma} {l} {_} (insertMaxRetainsElementsThere {_} {_} {k} {k'} {a} {a'} {r} prf)

{-# TERMINATING #-}
linkRetainsElementsHere : {{_ : Comparable K}} → {k : K} → {a : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ link k a ml mr
linkRetainsElementsHere {ml = tip} {mr = tip} = here
linkRetainsElementsHere {ml = tip} {mr = node rs rk ra rl rr} = balanceLRetainsElementsL {_} {_} {_} {rk} {_} {ra} {_} {rr} (insertMinRetainsElementsHere {_} {_} {_} {_} {rl})
linkRetainsElementsHere {ml = node ls lk la ll lr} {mr = tip} = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (insertMaxRetainsElementsHere {_} {_} {_} {_} {lr})
linkRetainsElementsHere {ml = node ls _ _ _ _} {mr = node rs _ _ _ _} with (compare (delta * ls) rs , compare (delta * rs) ls)
linkRetainsElementsHere {ml = l@(node _ _ _ _ _)} {mr = node _ rk ra rl rr} | (lt , lt) = balanceLRetainsElementsL {_} {_} {_} {rk} {_} {ra} {_} {rr} (linkRetainsElementsHere {_} {_} {_} {_} {l} {rl})
linkRetainsElementsHere {ml = l@(node _ _ _ _ _)} {mr = node _ rk ra rl rr} | (lt , gt) = balanceLRetainsElementsL {_} {_} {_} {rk} {_} {ra} {_} {rr} (linkRetainsElementsHere {_} {_} {_} {_} {l} {rl})
linkRetainsElementsHere {ml = l@(node _ _ _ _ _)} {mr = node _ rk ra rl rr} | (lt , eq) = balanceLRetainsElementsL {_} {_} {_} {rk} {_} {ra} {_} {rr} (linkRetainsElementsHere {_} {_} {_} {_} {l} {rl})
linkRetainsElementsHere {ml = node _ lk la ll lr} {mr = r@(node _ _ _ _ _)} | (gt , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsHere {_} {_} {_} {_} {lr} {r})
linkRetainsElementsHere {ml = node _ lk la ll lr} {mr = r@(node _ _ _ _ _)} | (eq , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsHere {_} {_} {_} {_} {lr} {r})
linkRetainsElementsHere {ml = node _ _ _ _ _} {mr = node _ _ _ _ _} | (gt , eq) = here
linkRetainsElementsHere {ml = node _ _ _ _ _} {mr = node _ _ _ _ _} | (gt , gt) = here
linkRetainsElementsHere {ml = node _ _ _ _ _} {mr = node _ _ _ _ _} | (eq , eq) = here
linkRetainsElementsHere {ml = node _ _ _ _ _} {mr = node _ _ _ _ _} | (eq , gt) = here

{-# TERMINATING #-}
linkRetainsElementsL : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ ml → (k , a) ∈ link k' a' ml mr
linkRetainsElementsL {ml = tip} {mr = node _ _ _ _ _} ()
linkRetainsElementsL {k = k} {k' = k'} {a = a} {a' = a'} {ml = node ls lk la ll lr} {mr = tip} here = balanceRRetainsElementsHere {_} {_} {_} {_} {ll} {insertMax k' a' lr}
linkRetainsElementsL {ml = node ls lk la ll lr} {mr = tip} (thereL prf) = balanceRRetainsElementsL prf
linkRetainsElementsL {k = k} {k' = k'} {a = a} {a' = a'} {ml = node ls lk la ll lr} {mr = tip} (thereR prf) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {insertMax k' a' lr} (insertMaxRetainsElementsThere prf)
linkRetainsElementsL {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here with (compare (delta * ls) rs , compare (delta * rs) ls)
... | (lt , gt) = balanceLRetainsElementsL {_} {_} {_} {_} {_} {_} {_} {_} (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} here)
... | (lt , lt) = balanceLRetainsElementsL {_} {_} {_} {_} {_} {_} {_} {_} (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} here)
... | (lt , eq) = balanceLRetainsElementsL {_} {_} {_} {_} {_} {_} {_} {_} (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} here)
... | (eq , lt) = balanceRRetainsElementsHere {_} {_} {_} {_} {ll} {link k' a' lr r}
... | (gt , lt) = balanceRRetainsElementsHere {_} {_} {_} {_} {ll} {link k' a' lr r}
... | (eq , eq) = thereL here
... | (eq , gt) = thereL here
... | (gt , eq) = thereL here
... | (gt , gt) = thereL here
linkRetainsElementsL {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) with (compare (delta * ls) rs , compare (delta * rs) ls)
... | (lt , gt) = balanceLRetainsElementsL (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} (thereL prf))
... | (lt , lt) = balanceLRetainsElementsL (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} (thereL prf))
... | (lt , eq) = balanceLRetainsElementsL (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} (thereL prf))
... | (eq , lt) = balanceRRetainsElementsL {_} {_} {_} {lk} {_} {la} {ll} {link k' a' lr r} prf
... | (gt , lt) = balanceRRetainsElementsL {_} {_} {_} {lk} {_} {la} {ll} {link k' a' lr r} prf
... | (eq , eq) = thereL (thereL prf)
... | (eq , gt) = thereL (thereL prf)
... | (gt , eq) = thereL (thereL prf)
... | (gt , gt) = thereL (thereL prf)
linkRetainsElementsL {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) with (compare (delta * ls) rs , compare (delta * rs) ls)
... | (lt , gt) = balanceLRetainsElementsL (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} (thereR prf))
... | (lt , lt) = balanceLRetainsElementsL (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} (thereR prf))
... | (lt , eq) = balanceLRetainsElementsL (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {l} {rl} (thereR prf))
... | (eq , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {link k' a' lr r} (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {lr} {r} prf)
... | (gt , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {link k' a' lr r} (linkRetainsElementsL {_} {_} {_} {k'} {_} {a'} {lr} {r} prf)
... | (eq , eq) = thereL (thereR prf)
... | (eq , gt) = thereL (thereR prf)
... | (gt , eq) = thereL (thereR prf)
... | (gt , gt) = thereL (thereR prf)

{-# TERMINATING #-}
linkRetainsElementsR : {{_ : Comparable K}} → {k k' : K} {a a' : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ mr → (k , a) ∈ link k' a' ml mr
linkRetainsElementsR {k = k} {k'} {a} {a'} {tip} {node rs rk ra rl rr} here = balanceLRetainsElementsHere {_} {_} {_} {_} {insertMin k' a' rl} {rr}
linkRetainsElementsR {k = k} {k'} {a} {a'} {tip} {node rs rk ra rl@(node rls rlk rla rll rlr) rr} (thereL here) = balanceLRetainsElementsL {_} {_} {_} {rk} {_} {ra} {_} {rr} (balanceLRetainsElementsHere {_} {_} {_} {_} {insertMin k' a' rll} {_})
linkRetainsElementsR {k = k} {k'} {a} {a'} {tip} {node rs rk ra rl@(node rls rlk rla rll rlr) rr} (thereL (thereL prf)) = balanceLRetainsElementsL (balanceLRetainsElementsL (insertMinRetainsElementsThere {_} {_} {_} {_} {_} {_} {rll} prf))
linkRetainsElementsR {k = k} {k'} {a} {a'} {tip} {node rs rk ra rl@(node rls rlk rla rll rlr) rr} (thereL (thereR prf)) = balanceLRetainsElementsL (balanceLRetainsElementsR {_} {_} {_} {rlk} {_} {rla} {insertMin k' a' rll} {_} prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {tip} {node rs rk ra rl rr} (thereR prf) = balanceLRetainsElementsR {_} {_} {_} {rk} {_} {ra} {insertMin k' a' rl} {_} prf
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here with (compare (delta * ls) rs , compare (delta * rs) ls)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (lt , lt) = balanceLRetainsElementsHere {_} {_} {_} {_} {link k' a' l rl} {_}
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (lt , gt) = balanceLRetainsElementsHere {_} {_} {_} {_} {link k' a' l rl} {_}
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (lt , eq) = balanceLRetainsElementsHere {_} {_} {_} {_} {link k' a' l rl} {_}
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (gt , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {lr} {_} here)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (eq , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {lr} {_} here)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (gt , gt) = thereR here
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (gt , eq) = thereR here
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (eq , gt) = thereR here
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} here | (eq , eq) = thereR here
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) with (compare (delta * ls) rs , compare (delta * rs) ls)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (lt , lt) = balanceLRetainsElementsL (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {l} {_} prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (lt , gt) = balanceLRetainsElementsL (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {l} {_} prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (lt , eq) = balanceLRetainsElementsL (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {l} {_} prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (gt , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {lr} {_} (thereL prf))
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (eq , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {lr} {_} (thereL prf))
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (gt , gt) = thereR (thereL prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (gt , eq) = thereR (thereL prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (eq , gt) = thereR (thereL prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereL prf) | (eq , eq) = thereR (thereL prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) with (compare (delta * ls) rs , compare (delta * rs) ls)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (lt , lt) = balanceLRetainsElementsR {_} {_} {_} {rk} {_} {ra} {link k' a' l rl} {_} prf
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (lt , gt) = balanceLRetainsElementsR {_} {_} {_} {rk} {_} {ra} {link k' a' l rl} {_} prf
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (lt , eq) = balanceLRetainsElementsR {_} {_} {_} {rk} {_} {ra} {link k' a' l rl} {_} prf
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (gt , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {lr} {_} (thereR prf))
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (eq , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} {_} (linkRetainsElementsR {_} {_} {_} {k'} {_} {a'} {lr} {_} (thereR prf))
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (gt , gt) = thereR (thereR prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (gt , eq) = thereR (thereR prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (eq , gt) = thereR (thereR prf)
linkRetainsElementsR {k = k} {k'} {a} {a'} {l@(node ls lk la ll lr)} {r@(node rs rk ra rl rr)} (thereR prf) | (eq , eq) = thereR (thereR prf) 


glueRetainsElementsR : {{_ : Comparable K}} → {k : K} → {a : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ mr → (k , a) ∈ glue ml mr
glueRetainsElementsR {ml = tip} here = here
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here with compare ls rs
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | gt with maxViewSure lk la ll lr
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | gt | maxview km m l' = balanceRRetainsElementsR {_} {_} {_} {km} {_} {m} {l'} {_} here
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | eq with minViewSure rk ra rl rr
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | eq | minview km m r' = balanceLRetainsElementsL {_} {_} {_} {km} {_} {m} {_} {r'} here
glueRetainsElementsR {ml = l@(node ls lk la ll lr)} {node rs rk ra rl rr} here | lt = {!   !}
glueRetainsElementsR {ml = tip} (thereL prf) = thereL prf
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) = {!   !}
glueRetainsElementsR {ml = tip} (thereR prf) = thereR prf
glueRetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) = glueRetainsElementsR (thereR prf)

link2RetainsElementsR : {{_ : Comparable K}} → {k : K} → {a : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ mr → (k , a) ∈ link2 ml mr
link2RetainsElementsR {ml = tip} {node rs rk ra rl rr} prf = prf
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here with (compare (delta * ls) rs , compare (delta * rs) ls)
link2RetainsElementsR {ml = l@(node ls lk la ll lr)} {node rs rk ra rl rr} here | (lt , lt) = balanceLRetainsElementsHere {_} {_} {_} {_} {link2 l rl} {rr}
link2RetainsElementsR {ml = l@(node ls lk la ll lr)} {node rs rk ra rl rr} here | (lt , gt) = balanceLRetainsElementsHere {_} {_} {_} {_} {link2 l rl} {rr}
link2RetainsElementsR {ml = l@(node ls lk la ll lr)} {node rs rk ra rl rr} here | (lt , eq) = balanceLRetainsElementsHere {_} {_} {_} {_} {link2 l rl} {rr}
link2RetainsElementsR {ml = l@(node ls lk la ll lr)} {node rs rk ra rl rr} here | (gt , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} (link2RetainsElementsR {_} {_} {_} {_} {lr} {_} here)
link2RetainsElementsR {ml = l@(node ls lk la ll lr)} {node rs rk ra rl rr} here | (eq , lt) = balanceRRetainsElementsR {_} {_} {_} {lk} {_} {la} {ll} (link2RetainsElementsR {_} {_} {_} {_} {lr} {_} here)
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | (gt , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | (gt , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | (eq , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} here | (eq , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) with (compare (delta * ls) rs , compare (delta * rs) ls)
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (lt , lt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (lt , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (lt , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (gt , lt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (eq , lt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (gt , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (gt , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (eq , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereL prf) | (eq , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) with (compare (delta * ls) rs , compare (delta * rs) ls)
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (lt , lt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (lt , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (lt , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (gt , lt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (eq , lt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (gt , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (gt , eq) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (eq , gt) = {!   !}
link2RetainsElementsR {ml = node ls lk la ll lr} {node rs rk ra rl rr} (thereR prf) | (eq , eq) = {!   !}

link2RetainsElementsL : {{_ : Comparable K}} → {k : K} → {a : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ ml → (k , a) ∈ link2 ml mr
link2RetainsElementsL {ml = node ls lk la ll lr} {tip} prf = prf
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf with (compare (delta * ls) rs , compare (delta * rs) ls)
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (lt , lt) = balanceLRetainsElementsL (link2RetainsElementsL {_} {_} {_} {_} {_} {rl} prf)
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (lt , gt) = balanceLRetainsElementsL (link2RetainsElementsL {_} {_} {_} {_} {_} {rl} prf)
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (lt , eq) = balanceLRetainsElementsL (link2RetainsElementsL {_} {_} {_} {_} {_} {rl} prf)
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (gt , lt) = {! balanceRRetainsElementsR (link2RetainsElementsR prf)  !}
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (eq , lt) = {!   !}
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (gt , gt) = {!   !}
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (gt , eq) = {!   !}
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (eq , gt) = {!   !}
link2RetainsElementsL {ml = node ls lk la ll lr} {node rs rk ra rl rr} prf | (eq , eq) = {!   !}