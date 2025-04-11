module Map.Test.Balance.BalanceL where

open import Agda.Builtin.Nat

open import Map.Map
open import Map.Balance
open import Map.Test.Cases
open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A : Set

balanceLRetainsElementsHere : {{_ : Comparable K}} → {k : K} → {a : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ balanceL k a ml mr
balanceLRetainsElementsHere {ml = tip} {mr = tip} = here
balanceLRetainsElementsHere {ml = node _ _ _ tip tip} {mr = tip} = here
balanceLRetainsElementsHere {ml = node _ _ _ tip (node _ _ _ _ _)} {mr = tip} = thereR here
balanceLRetainsElementsHere {ml = node _ _ _ (node _ _ _ _ _) tip} {mr = tip} = thereR here
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = tip} with compare lrs (ratio * lls)
... | lt = thereR here
... | eq = thereR here
... | gt = thereR here
balanceLRetainsElementsHere {ml = tip} {mr = node _ _ _ _ _} = here
balanceLRetainsElementsHere {ml = node ls _ _ (node _ _ _ _ _) (node _ _ _ _ _)} {mr = node rs _ _ _ _} with compare rs (delta * ls)
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = node _ _ _ _ _} | gt with compare lrs (ratio * lls)
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = node _ _ _ _ _} | gt | lt = thereR here
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = node _ _ _ _ _} | gt | eq = thereR here
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = node _ _ _ _ _} | gt | gt = thereR here
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = node _ _ _ _ _} | lt = here
balanceLRetainsElementsHere {ml = node _ _ _ (node lls _ _ _ _) (node lrs _ _ _ _)} {mr = node _ _ _ _ _} | eq = here
balanceLRetainsElementsHere {ml = node ls _ _ tip (node _ _ _ _ _)} {mr = node rs _ _ _ _} with compare rs (delta * ls)
... | gt = here
... | lt = here
... | eq = here
balanceLRetainsElementsHere {ml = node ls _ _ (node _ _ _ _ _) tip} {mr = node rs _ _ _ _} with compare rs (delta * ls)
... | gt = here
... | lt = here
... | eq = here
balanceLRetainsElementsHere {ml = node ls _ _ tip tip} {mr = node rs _ _ _ _} with compare rs (delta * ls)
... | gt = here
... | lt = here
... | eq = here

balanceLRetainsElementsL : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ ml → (k , a) ∈ balanceL k' a' ml mr
balanceLRetainsElementsL {ml = node ls lk la tip tip} {tip} prf = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {tip} here = thereL here
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {tip} (thereR here) = here
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {tip} (thereR (thereL prf)) = {! not possible  !}
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {tip} (thereR (thereR prf)) = {! not possible!  !}
balanceLRetainsElementsL {ml = node ls lk la (node _ _ _ _ _) tip} {tip} here = here
balanceLRetainsElementsL {ml = node ls lk la (node _ _ _ _ _) tip} {tip} (thereL prf) = thereL prf
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} here with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} here | lt = here
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} here | gt = thereL here
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} here | eq = thereL here
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereL prf) with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereL prf) | lt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereL prf) | gt = thereL (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereL prf) | eq = thereL (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR here) with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR here) | lt = thereR (thereL here)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR here) | gt = here
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR here) | eq = here
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereR prf)) with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereR prf)) | lt = thereR (thereL (thereR prf))
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereR prf)) | gt = thereR (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereR prf)) | eq = thereR (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereL prf)) with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereL prf)) | lt = thereR (thereL (thereL prf))
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereL prf)) | gt = thereL (thereR prf)
balanceLRetainsElementsL {ml = node ls lk la (node lls _ _ _ _) (node lrs _ _ _ _)} {tip} (thereR (thereL prf)) | eq = thereL (thereR prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here | gt with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here | gt | lt = here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here | gt | gt = thereL here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here | gt | eq = thereL here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here | lt = thereL here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} here | eq = thereL here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) | gt with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) | gt | lt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) | gt | gt = thereL (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) | gt | eq = thereL (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) | lt = thereL (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereL prf) | eq = thereL (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) | gt with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) | gt | lt = thereR (thereL here)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) | gt | gt = here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) | gt | eq = here
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) | lt = thereL (thereR here)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR here) | eq = thereL (thereR here)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) | gt with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) | gt | lt = thereR (thereL (thereL prf))
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) | gt | gt = thereL (thereR prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) | gt | eq = thereL (thereR prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) | lt = thereL (thereR (thereL prf))
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereL prf)) | eq = thereL (thereR (thereL prf))
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) | gt with compare lrs (ratio * lls)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) | gt | lt = thereR (thereL (thereR prf))
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) | gt | gt = thereR (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) | gt | eq = thereR (thereL prf)
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) | lt = thereL (thereR (thereR prf))
balanceLRetainsElementsL {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} (thereR (thereR prf)) | eq = thereL (thereR (thereR prf))
balanceLRetainsElementsL {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf | gt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf | lt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf | eq = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf | gt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf | lt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf | eq = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsL {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf | gt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf | lt = thereL prf
balanceLRetainsElementsL {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf | eq = thereL prf



balanceLRetainsElementsR : {{_ : Comparable K}} → {k k' : K} → {a a' : A} → {ml : Map K A} → {mr : Map K A} → (k , a) ∈ mr → (k , a) ∈ balanceL k' a' ml mr
balanceLRetainsElementsR {ml = tip} here = thereR here
balanceLRetainsElementsR {ml = tip} (thereL prf) = thereR (thereL prf)
balanceLRetainsElementsR {ml = tip} (thereR prf) = thereR (thereR prf)
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf | gt with compare lrs (ratio * lls)
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf | gt | lt = thereR (thereR prf)
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf | gt | gt = thereR (thereR prf)
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf | gt | eq = thereR (thereR prf)
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf | lt = thereR prf
balanceLRetainsElementsR {ml = node ls lk la ll@(node lls _ _ _ _) lr@(node lrs _ _ _ _)} {node rs rk ra rl rr} prf | eq = thereR prf
balanceLRetainsElementsR {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsR {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf | gt = thereR prf
balanceLRetainsElementsR {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf | eq = thereR prf
balanceLRetainsElementsR {ml = node ls lk la (node _ _ _ _ _) tip} {node rs rk ra rl rr} prf | lt = thereR prf
balanceLRetainsElementsR {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsR {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf | gt = thereR prf
balanceLRetainsElementsR {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf | eq = thereR prf
balanceLRetainsElementsR {ml = node ls lk la tip (node _ _ _ _ _)} {node rs rk ra rl rr} prf | lt = thereR prf
balanceLRetainsElementsR {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf with compare rs (delta * ls)
balanceLRetainsElementsR {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf | gt = thereR prf
balanceLRetainsElementsR {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf | eq = thereR prf
balanceLRetainsElementsR {ml = node ls lk la tip tip} {node rs rk ra rl rr} prf | lt = thereR prf