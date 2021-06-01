module Data.Map.Internal.Unions where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.PreconditionProofs

module Unions {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  unions : ∀ {lower upper : [ k ]∞} → ⦃ Foldable f ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a {lower} {upper}) ⦄ → f (Map k a {lower} {upper}) → Map k a {lower} {upper}

  unionsWith : ∀ {lower upper : [ k ]∞} → ⦃ Foldable f ⦄ → (a → a → a) → f (Map k a {lower} {upper}) → Map k a {lower} {upper}

  union : ∀ {lower upper : [ k ]∞} → ⦃ Eq a ⦄ → ⦃ Eq (Map k a {lower} {upper}) ⦄ → Map k a {lower} {upper} → Map k a {lower} {upper} → Map k a {lower} {upper}

  unionWith : ∀ {lower upper : [ k ]∞}  → (a → a → a) → Map k a {lower} {upper} → Map k a {lower} {upper} → Map k a {lower} {upper}

  unionWithKey : ∀ {lower upper : [ k ]∞} → (k → a → a → a) → Map k a {lower} {upper} → Map k a {lower} {upper} → Map k a {lower} {upper}


open Unions public
