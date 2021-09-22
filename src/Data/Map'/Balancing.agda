{-# OPTIONS --warning noMissingDefinitions #-}

module Data.Map'.Balancing where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map'.Datatype
{-# FOREIGN AGDA2HS
import Data.Map'.Datatype
#-}

module Balancing {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  delta : Int
  delta = 3

  ratio : Int
  ratio = 2

  balance : ∀ {l1 u1 l2 u2 : [ k ]∞} → (kx : k) → a
          → {{u1≤k : u1 ≤ [ kx ]}} {{k≤l2 : [ kx ] ≤ l2}}
          → Map k a {l1} {u1} → Map k a {l2} {u2}
          → Map k a {l1} {u2}

open Balancing public
