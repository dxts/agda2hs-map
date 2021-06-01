{-# OPTIONS --warning noMissingDefinitions #-}

module Data.Map.Internal.Balancing where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Balancing {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  delta : Int
  delta = 3

  ratio : Int
  ratio = 2

  balance : ∀ {lower upper : [ k ]∞} → (kx : k) → a
          → Map k a {lower} {[ kx ]} → Map k a {[ kx ]} {upper}
          → Map k a {lower} {upper}

  balanceL : ∀ {lower upper : [ k ]∞} → (kx : k) → a
          → Map k a {lower} {[ kx ]} → Map k a {[ kx ]} {upper}
          → Map k a {lower} {upper}

  balanceR : ∀ {lower upper : [ k ]∞} → (kx : k) → a
          → Map k a {lower} {[ kx ]} → Map k a {[ kx ]} {upper}
          → Map k a {lower} {upper}

open Balancing public
