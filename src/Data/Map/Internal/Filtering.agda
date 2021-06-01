module Data.Map.Internal.Filtering where

open import Haskell.Prelude hiding (filter)
{-# FOREIGN AGDA2HS
import Prelude hiding (filter)
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Filtering {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  filter : ∀ {lower upper : [ k ]∞} → (a -> Bool) -> Map k a {lower} {upper} -> Map k a {lower} {upper}

  filterWithKey : ∀ {lower upper : [ k ]∞} → (k -> a -> Bool) -> Map k a {lower} {upper} -> Map k a {lower} {upper}

  filterWithKeyA : ∀ {lower upper : [ k ]∞} → {f : Set → Set} → ⦃ Applicative f ⦄ → (k -> a -> f Bool) -> Map k a {lower} {upper} -> f (Map k a {lower} {upper})

  takeWhileAntitone : ∀ {lower upper : [ k ]∞} → (k -> Bool) -> Map k a {lower} {upper} -> Map k a {lower} {upper}

  dropWhileAntitone : ∀ {lower upper : [ k ]∞} → (k -> Bool) -> Map k a {lower} {upper} -> Map k a {lower} {upper}

  spanAntitone : ∀ {lower upper : [ k ]∞} → (k -> Bool) -> Map k a {lower} {upper} -> (Map k a {lower} {upper}) × (Map k a {lower} {upper})

  partition : ∀ {lower upper : [ k ]∞} → (a -> Bool) -> Map k a {lower} {upper} -> (Map k a {lower} {upper}) × (Map k a {lower} {upper})

  partitionWithKey : ∀ {lower upper : [ k ]∞} → (k -> a -> Bool) -> Map k a {lower} {upper} -> (Map k a {lower} {upper}) × (Map k a {lower} {upper})

  mapMaybe : ∀ {lower upper : [ k ]∞} → (a -> Maybe b) -> Map k a {lower} {upper} -> Map k b {lower} {upper}

  mapMaybeWithKey : ∀ {lower upper : [ k ]∞} → (k -> a -> Maybe b) -> Map k a {lower} {upper} -> Map k b {lower} {upper}

  traverseMaybeWithKey : {b : Set} → ∀ {lower upper : [ k ]∞} → {f : Set → Set} → ⦃ Applicative f ⦄ → (k -> a -> f (Maybe b)) -> Map k a {lower} {upper} -> f (Map k b {lower} {upper})

  mapEither : {b c : Set} → ∀ {lower upper : [ k ]∞} → (a -> Either b c) -> Map k a {lower} {upper} -> (Map k b {lower} {upper}) × (Map k c {lower} {upper})

  mapEitherWithKey : {b c : Set} → ∀ {lower upper : [ k ]∞} → (k -> a -> Either b c) -> Map k a {lower} {upper} -> (Map k b {lower} {upper}) × (Map k c {lower} {upper})


open Filtering public
