module Data.Map.Internal.Splitting where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Splitting {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  split : ∀ {lower upper : [ k ]∞} → k → Map k a {lower} {upper} → (Map k a {lower} {upper} × Map k a {lower} {upper})

  splitLookup : ∀ {lower upper : [ k ]∞} → k → Map k a {lower} {upper} → (Map k a {lower} {upper} × Maybe a × Map k a {lower} {upper})

  splitMember : ∀ {lower upper : [ k ]∞} → k → Map k a {lower} {upper} → (Map k a {lower} {upper} × Bool × Map k a {lower} {upper})

open Splitting public
