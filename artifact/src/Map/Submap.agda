module Map.Submap where

open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe

open import Map.Query
open import Map.Map
-- open import Map.Filter

private variable
  K A B : Set

submap' : {{Comparable K}} → (A → B → Bool) → Map K A → Map K B → Bool
submap' _ tip _ = true
submap' _ _ tip = false
submap' f (node 1 kx x _ _) t with lookup kx t
...                           | just y = f x y
...                           | nothing = false
submap' f (node _ kx x l r) t with splitLookup kx t
...                           | (_ , nothing , _) = false
-- ...                           | (lt' , just y , gt') = size l <= size lt' && size r <= size gt' && submap' f l lt' && submap' f r gt'
...                           | (lt' , just y , gt') with (compare (size l) (size lt') , compare (size r) (size gt'))
...                                                  | (gt , _) = false
...                                                  | (_ , gt) = false
...                                                  | (_ , _) = submap' f l lt' && submap' f r gt'

isSubmapOfBy : {{Comparable K}} → (A → B → Bool) → Map K A → Map K B → Bool
isSubmapOfBy f t1 t2 with compare (size t1) (size t2)
...                  | gt = false
...                  | _ = submap' f t1 t2

isSubmapOf : {{Comparable K}} → {{Equal A}} → Map K A → Map K A → Bool
isSubmapOf m1 m2 = isSubmapOfBy equal m1 m2

isProperSubmapOfBy : {{Comparable K}} → (A → B → Bool) → Map K A → Map K B → Bool
isProperSubmapOfBy f t1 t2 with compare (size t1) (size t2)
...                        | lt = submap' f t1 t2
...                        | _ = false

isProperSubmapOf : {{Comparable K}} → {{Equal A}} → Map K A → Map K A → Bool
isProperSubmapOf m1 m2 = isProperSubmapOfBy equal m1 m2