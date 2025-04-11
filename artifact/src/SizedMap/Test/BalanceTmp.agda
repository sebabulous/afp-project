module Map.Test.BalanceTmp where

open import Agda.Builtin.Nat

open import Map.Map
open import Map.Balance
open import Map.Test.Cases
open import Map.Test.Balance

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