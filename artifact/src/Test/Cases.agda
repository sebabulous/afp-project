module Test.Cases where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Map.Construction
open import Map.Map

KV5a = 5 , "a"
KV5aUpdate = 5 , "5:a"
KV3b = 3 , "b"
KV3bUpdate = 3 , "3:b"
KV7c = 7 , "c"

testEmpty : Map Nat String
testEmpty = tip -- fromList []

test53 : Map Nat String
test53 = node 2 (Pair.fst KV5a) (Pair.snd KV5a) 
        (node 1 (Pair.fst KV3b) (Pair.snd KV3b) tip tip) tip 
        -- fromList (KV5a ∷ KV3b ∷ [])

test35 : Map Nat String
test35 = node 2 (Pair.fst KV3b) (Pair.snd KV3b) 
        tip (node 1 (Pair.fst KV5a) (Pair.snd KV5a) tip tip)
        -- fromList (KV3b ∷ KV5a ∷ []) 

test35update3 : Map Nat String
test35update3 = node 2 (Pair.fst KV5a) (Pair.snd KV5a) 
        (node 1 (Pair.fst KV3bUpdate) (Pair.snd KV3bUpdate) tip tip) tip 
        -- fromList (KV3bUpdate ∷ KV5a ∷ []) 

test35update5 : Map Nat String
test35update5 = node 2 (Pair.fst KV5aUpdate) (Pair.snd KV5aUpdate) 
        (node 1 (Pair.fst KV3b) (Pair.snd KV3b) tip tip) tip 
        -- fromList (KV3b ∷ KV5aUpdate ∷ []) 

test35update35 : Map Nat String
test35update35 = node 2 (Pair.fst KV5aUpdate) (Pair.snd KV5aUpdate) 
        (node 1 (Pair.fst KV3bUpdate) (Pair.snd KV3bUpdate) tip tip) tip 
        -- fromList (KV3b ∷ KV5aUpdate ∷ []) 

test35addX : Map Nat String
test35addX = node 2 (Pair.fst KV3b) "bx"
        tip (node 1 (Pair.fst KV5a) "ax" tip tip)

test35add1 : Map Nat String
test35add1 = node 2 (Pair.fst KV3b + 1) (Pair.snd KV3b) 
        tip (node 1 (Pair.fst KV5a + 1) (Pair.snd KV5a) tip tip)

test35times2 : Map Nat String
test35times2 = node 2 (Pair.fst KV3b * 2) (Pair.snd KV3b) 
        tip (node 1 (Pair.fst KV5a * 2) (Pair.snd KV5a) tip tip)

test57 : Map Nat String
test57 = node 2 (Pair.fst KV5a) (Pair.snd KV5a) 
        tip (node 1 (Pair.fst KV7c) (Pair.snd KV7c) tip tip) 
        -- fromList (KV5a ∷ KV7c ∷ [])
        
test537 : Map Nat String
test537 = node 3 (Pair.fst KV5a) (Pair.snd KV5a) 
        (node 1 (Pair.fst KV3b) (Pair.snd KV3b) tip tip) 
        (node 1 (Pair.fst KV7c) (Pair.snd KV7c) tip tip) 
        -- fromList (KV5a ∷ KV3b ∷ KV7c ∷ [])