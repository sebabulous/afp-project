module SizedMap.Submap where

open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

open import SizedMap.Query
open import SizedMap.Map
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Filter

private variable
  K A B : Set
  m n : Nat

submap' : {{Comparable K}} → (A → B → Bool) → Map K A m → Map K B n → Bool
submap' _ tip _ = true
submap' _ _ tip = false
submap' f (node kx x tip tip) t with lookup kx t
...                           | just y = f x y
...                           | nothing = false
submap' f (node kx x l r) t with splitLookup kx t
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ _ nothing _)) = false
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) with compare (size l) m'
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | gt = false
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | lt with compare (size r) n'
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | lt | gt = false
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | lt | eq = submap' f l lt' && submap' f r gt'
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | lt | lt = submap' f l lt' && submap' f r gt'
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | eq with compare (size r) n'
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | eq | gt = false
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | eq | eq = submap' f l lt' && submap' f r gt'
submap' f (node kx x l r) t | ((m' , n') , (_,_,_ lt' (just y) gt')) | eq | lt = submap' f l lt' && submap' f r gt'

isSubmapOfBy : {{Comparable K}} → (A → B → Bool) → Map K A m → Map K B n → Bool
isSubmapOfBy f t1 t2 with compare (size t1) (size t2)
...                  | gt = false
...                  | _ = submap' f t1 t2

isSubmapOf : {{Comparable K}} → {{Equal A}} → Map K A m → Map K A n → Bool
isSubmapOf m1 m2 = isSubmapOfBy equal m1 m2

isProperSubmapOfBy : {{Comparable K}} → (A → B → Bool) → Map K A m → Map K B n → Bool
isProperSubmapOfBy f t1 t2 with compare (size t1) (size t2)
...                        | lt = submap' f t1 t2
...                        | _ = false

isProperSubmapOf : {{Comparable K}} → {{Equal A}} → Map K A m → Map K A n → Bool
isProperSubmapOf m1 m2 = isProperSubmapOfBy equal m1 m2