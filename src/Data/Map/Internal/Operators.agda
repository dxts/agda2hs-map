module Data.Map.Internal.Operators where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.PreconditionProofs

module Operators {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  _!_ :  ∀ {lower upper : [ k ]∞} → (map : Map k a {lower} {upper}) → (key : k) → {key ∈ map} → a

  _!?_ : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → k → Maybe a

  _\\_ : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k a {lower} {upper}

open Operators public
