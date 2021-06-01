module Data.Map.Internal.Deletion where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Deletion {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  delete : ∀ {lower upper : [ k ]∞} → ⦃ Eq (Map k a {lower} {upper}) ⦄ → k → Map k a {lower} {upper} → Map k a {lower} {upper}

  adjust : ∀ {lower upper : [ k ]∞} → (a → a) → k → Map k a {lower} {upper} → Map k a {lower} {upper}

  adjustWithKey : ∀ {lower upper : [ k ]∞} → (k → a → a) → k → Map k a {lower} {upper} → Map k a {lower} {upper}

  update : ∀ {lower upper : [ k ]∞} → (a → Maybe a) → k → Map k a {lower} {upper} → Map k a {lower} {upper}

  updateWithKey : ∀ {lower upper : [ k ]∞} → (k → a → Maybe a) → k → Map k a {lower} {upper} → Map k a {lower} {upper}

  updateLookupWithKey : ∀ {lower upper : [ k ]∞} → (k → a → Maybe a) → k → Map k a {lower} {upper} → (Maybe a × Map k a {lower} {upper})

  alter : ∀ {lower upper : [ k ]∞} → (Maybe a → Maybe a) → k → Map k a {lower} {upper} → Map k a {lower} {upper}

  -- [TODO] `alterF` and related methods


open Deletion public
