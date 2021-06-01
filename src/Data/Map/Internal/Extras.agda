module Data.Map.Internal.Extras where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Extras {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  bin : ∀ {lower upper : [ k ]∞} → k → a → Map k a {lower} {upper} → Map k a {lower} {upper} → Map k a {lower} {upper}

  splitRoot : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → List (Map k a {lower} {upper})


open Extras public
