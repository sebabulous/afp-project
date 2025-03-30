module Benchmarks.Map where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Map.Map
open import Map.Construction using (fromList)
-- open import Map.Combine using (intersection)
open import Map.Query using (lookup)
open import Map.Insertion using (insert)

--------------------------------------------------------------------------------
-- Insert Int

-- Start with empty map
insertMapLazy : Nat → Map Nat Nat → Map Nat Nat
insertMapLazy zero y = y
insertMapLazy (suc x) y = insertMapLazy x (insert (suc x) (suc x) y)  --  go n !acc = go (n - 1) (insert n n acc)