module Data.Map.Internal.Mapping where

open import Haskell.Prelude hiding (map)
{-# FOREIGN AGDA2HS
import Prelude hiding (map)
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.PreconditionProofs


module Mapping {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  map : ∀ {lower upper : [ k ]∞} → (a -> b) -> Map k a -> Map k b

  mapWithKey : ∀ {lower upper : [ k ]∞} → (k -> a -> b) -> Map k a -> Map k b

  traverseWithKey : ∀ {lower upper : [ k ]∞} → {t : Set → Set} → ⦃ Applicative t ⦄ → (k -> a -> t b) -> Map k a -> t (Map k b)

  mapAccum : {b c : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)

  mapAccumWithKey : {b c : Set} → ∀ {lower upper : [ k ]∞} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)

  mapAccumL : {b c : Set} → ∀ {lower upper : [ k ]∞} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)

  mapAccumRWithKey : {b c : Set} → ∀ {lower upper : [ k ]∞} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)

  mapKeys : {k2 : Set} ⦃ iOrdk2 : Ord k2 ⦄ → ⦃ Eq a ⦄ → ∀ {lower upper : [ k ]∞} → ∀ {lower2 upper2 : [ k2 ]∞} → ⦃ Eq (Map k2 a) ⦄ -> (k -> k2) -> Map k a -> Map k2 a

  mapKeysWith : {k2 : Set} ⦃ iOrdk2 : Ord k2 ⦄ -> ∀ {lower upper : [ k ]∞} → ∀ {lower2 upper2 : [ k2 ]∞} → (a -> a -> a) -> (k -> k2) -> Map k a -> Map k2 a

  mapKeysMonotonic : {k2 : Set} ⦃ iOrdk2 : Ord k2 ⦄ → ∀ {lower upper : [ k ]∞} → ∀ {lower2 upper2 : [ k2 ]∞} → (k -> k2) -> Map k a -> Map k2 a

open Mapping public
