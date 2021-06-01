module Data.Map.Internal.Merging where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.PreconditionProofs


module Merging {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  -- [TODO] `merge` function and it's helpers.

  mergeWithKey : {b c : Set} ⦃ iOrdb : Ord b ⦄ → ∀ {lower upper : [ k ]∞} → (k → a → b → Maybe c)
               → (Map k a {lower} {upper} → Map k c {lower} {upper}) → (Map k b {lower} {upper} → Map k c {lower} {upper})
               → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k c {lower} {upper}

open Merging public
