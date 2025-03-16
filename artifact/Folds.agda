{-# OPTIONS --allow-unsolved-metas #-}
module artifact.Folds where

open import artifact.Main

foldr : {V K A : Set} → (A → V → V) → V → Map K A → V
foldr = {!   !}

foldl : {V K A : Set} → (V → A → V) → V → Map K A → V
foldl = {!   !}

foldrWithKey : {V K A : Set} → (K → A → V → V) → V → Map K A → V
foldrWithKey = {!   !}

foldlWithKey : {V K A : Set} → (V → K → A → V) → V → Map K A → V
foldlWithKey = {!   !}

-- foldMapWithKey


-- %%%%%%%%%%%%% Strict folds %%%%%%%%%%%%%%%%%%%%%%

foldr' : {V K A : Set} → (A → V → V) → V → Map K A → V
foldr' = {!   !}

foldl' : {V K A : Set} → (V → A → V) → V → Map K A → V
foldl' = {!   !}

foldrWithKey' : {V K A : Set} → (K → A → V → V) → V → Map K A → V
foldrWithKey' = {!   !}

foldlWithKey' : {V K A : Set} → (V → K → A → V) → V → Map K A → V
foldlWithKey' = {!   !}