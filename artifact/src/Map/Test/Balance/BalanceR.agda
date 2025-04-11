module Map.Test.Balance.BalanceR where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

open import Map.Map
open import Map.Balance
open import Helpers.Comparable
open import Helpers.Pair
open import Map.Test.Cases

private variable
  K A : Set

balanceRRetainsElementsHere : {{_ : Comparable K}} → {k : K} → {a : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ balanceR k a ml mr
balanceRRetainsElementsHere {ml = tip} {mr = tip} = here
balanceRRetainsElementsHere {ml = tip} {mr = node _ _ _ tip tip} = here
balanceRRetainsElementsHere {ml = tip} {mr = node _ _ _ tip (node _ _ _ _ _)} = thereL here
balanceRRetainsElementsHere {ml = tip} {mr = node _ _ _ (node _ _ _ _ _) tip} = thereL here
balanceRRetainsElementsHere {ml = tip} {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} with rls < ratio * rrs
... | true = thereL here
... | false = thereL here
balanceRRetainsElementsHere {ml = node _ _ _ _ _} {mr = tip} = here
balanceRRetainsElementsHere {ml = node ls _ _ _ _} {mr = node rs _ _ _ _} with compare rs (delta * ls)
balanceRRetainsElementsHere {mr = node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} | gt with compare rls (ratio * rrs)
...   | lt = thereL here
...   | eq = thereL here
...   | gt = thereL here
balanceRRetainsElementsHere {mr = node _ _ _ tip (node _ _ _ _ _)} | gt = here
balanceRRetainsElementsHere {mr = node _ _ _ (node _ _ _ _ _) tip} | gt = here
balanceRRetainsElementsHere {mr = node _ _ _ tip tip} | gt = here
balanceRRetainsElementsHere | eq = here
balanceRRetainsElementsHere | lt = here

balanceRRetainsElementsL : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ ml → (k , a) ∈ balanceR k' a' ml mr
balanceRRetainsElementsL {mr = tip} here = thereL here
balanceRRetainsElementsL {ml = node ls _ _ _ _} {mr = node rs _ _ _ _} prf with compare rs (delta * ls)
balanceRRetainsElementsL {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} here | gt with compare rls (ratio * rrs)
... | lt = thereL (thereL here)
... | eq = thereL (thereL here)
... | gt = thereL (thereL here)
balanceRRetainsElementsL {mr = node _ _ _ (node rls _ _ _ _) rr@(node rrs _ _ _ _)} (thereL prf) | gt with compare rls (ratio * rrs)
... | lt = thereL (thereL (thereL prf))
... | eq = thereL (thereL (thereL prf))
... | gt = thereL (thereL (thereL prf))
balanceRRetainsElementsL {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereR prf) | gt with compare rls (ratio * rrs)
... | lt = thereL (thereL (thereR prf))
... | eq = thereL (thereL (thereR prf))
... | gt = thereL (thereL (thereR prf))
balanceRRetainsElementsL {mr = node _ _ _ tip (node _ _ _ _ _)} here | gt = thereL here
balanceRRetainsElementsL {mr = node _ _ _ tip (node _ _ _ _ _)} (thereL prf) | gt = thereL (thereL prf)
balanceRRetainsElementsL {mr = node _ _ _ tip (node _ _ _ _ _)} (thereR prf) | gt = thereL (thereR prf)
balanceRRetainsElementsL {mr = node _ _ _ (node _ _ _ _ _) tip} here | gt = thereL here
balanceRRetainsElementsL {mr = node _ _ _ (node _ _ _ _ _) tip} (thereL prf) | gt = thereL (thereL prf)
balanceRRetainsElementsL {mr = node _ _ _ (node _ _ _ _ _) tip} (thereR prf) | gt = thereL (thereR prf)
balanceRRetainsElementsL {mr = node _ _ _ tip tip} here | gt = thereL here
balanceRRetainsElementsL {mr = node _ _ _ tip tip} (thereL prf) | gt = thereL (thereL prf)
balanceRRetainsElementsL {mr = node _ _ _ tip tip} (thereR prf) | gt = thereL (thereR prf)
balanceRRetainsElementsL here | eq = thereL here
balanceRRetainsElementsL (thereL prf) | eq = thereL (thereL prf)
balanceRRetainsElementsL (thereR prf) | eq = thereL (thereR prf)
balanceRRetainsElementsL here | lt = thereL here
balanceRRetainsElementsL (thereL prf) | lt = thereL (thereL prf)
balanceRRetainsElementsL (thereR prf) | lt = thereL (thereR prf)
balanceRRetainsElementsL {mr = tip} (thereL prf) = thereL (thereL prf)
balanceRRetainsElementsL {mr = tip} (thereR prf) = thereL (thereR prf)

balanceRRetainsElementsR : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ mr → (k , a) ∈ balanceR k' a' ml mr
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ tip tip} prf = thereR prf
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ tip (node _ _ _ _ _)} here = here
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ tip (node _ _ _ _ _)} (thereR prf) = thereR prf
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node _ _ _ _ _) tip} here = thereR here
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node _ _ _ _ _) tip} (thereL here) = here
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node _ _ _ _ _) tip} _ = {!  not possible! !}
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} here with rls < ratio * rrs
... | true = here
... | false = thereR here
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereR prf) with rls < ratio * rrs
... | true = thereR prf
... | false = thereR (thereR prf)
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL here) with rls < ratio * rrs
... | true = thereL (thereR here)
... | false = here
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL (thereL prf)) with rls < ratio * rrs
... | true = thereL (thereR (thereL prf))
... | false = thereL (thereR prf)
balanceRRetainsElementsR {ml = tip} {mr = node _ _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL (thereR prf)) with rls < ratio * rrs
... | true = thereL (thereR (thereR prf))
... | false = thereR (thereL prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} prf with compare rs (delta * ls)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} prf | gt with compare rls (ratio * rrs)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} here | gt | lt = here
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL prf) | gt | lt = thereL (thereR prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereR prf) | gt | lt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} here | gt | eq = thereR here
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL here) | gt | eq = here
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL (thereL prf)) | gt | eq = thereL (thereR prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL (thereR prf)) | gt | eq = thereR (thereL prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereR prf) | gt | eq = thereR (thereR prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} here | gt | gt = thereR here
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL here) | gt | gt = here
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL (thereL prf)) | gt | gt = thereL (thereR prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereL (thereR prf)) | gt | gt = thereR (thereL prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} (thereR prf) | gt | gt = thereR (thereR prf)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} prf | lt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node rls _ _ _ _) (node rrs _ _ _ _)} prf | eq = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ tip (node _ _ _ _ _)} prf with compare rs (delta * ls)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ tip (node _ _ _ _ _)} prf | gt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ tip (node _ _ _ _ _)} prf | eq = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ tip (node _ _ _ _ _)} prf | lt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node _ _ _ _ _) tip} prf with compare rs (delta * ls)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node _ _ _ _ _) tip} prf | gt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node _ _ _ _ _) tip} prf | eq = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ (node _ _ _ _ _) tip} prf | lt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ tip tip} prf with compare rs (delta * ls)
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ tip tip} prf | gt = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ _ _} prf | eq = thereR prf
balanceRRetainsElementsR {ml = node ls _ _ _ _} {node rs _ _ _ _} prf | lt = thereR prf