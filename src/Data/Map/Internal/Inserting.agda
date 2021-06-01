module Data.Map.Internal.Inserting where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}


open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Inserting {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  insert : ∀ {lower upper : [ k ]∞} → ⦃ Eq a ⦄ → ⦃ Eq (Map k a {lower} {upper}) ⦄ → k → a → (m : Map k a {lower} {upper}) → Map k a {lower} {upper}

  insertR : ∀ {lower upper : [ k ]∞} → ⦃ Eq a ⦄ → ⦃ Eq (Map k a {lower} {upper}) ⦄ → k → a → (m : Map k a {lower} {upper}) → Map k a {lower} {upper}

  insertWith : ∀ {lower upper : [ k ]∞} → (a → a → a) → k → a → Map k a {lower} {upper} → Map k a {lower} {upper}

  insertWithR : ∀ {lower upper : [ k ]∞} → (a → a → a) → k → a → Map k a {lower} {upper} → Map k a {lower} {upper}

  insertWithKey : ∀ {lower upper : [ k ]∞} → (k → a → a → a) → k → a → Map k a {lower} {upper} → Map k a {lower} {upper}

  insertWithKeyR : ∀ {lower upper : [ k ]∞} → (k → a → a → a) → k → a → Map k a {lower} {upper} → Map k a {lower} {upper}

  insertLookupWithKey : ∀ {lower upper : [ k ]∞} → (k → a → a → a) → k → a → Map k a {lower} {upper} → (Maybe a × Map k a {lower} {upper})


open Inserting public
