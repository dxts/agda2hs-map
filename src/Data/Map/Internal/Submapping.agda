module Data.Map.Internal.Submapping where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.PreconditionProofs

module Submapping {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  isSubmapOf : ∀ {lower upper : [ k ]∞} → ⦃ Eq a ⦄ → Map k a {lower} {upper} -> Map k a {lower} {upper} -> Bool

  isSubmapOfBy : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> Bool) -> Map k a {lower} {upper} -> Map k b {lower} {upper} -> Bool

  submap' : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> Bool) -> Map k a {lower} {upper} -> Map k b {lower} {upper} -> Bool

  isProperSubmapOf : ∀ {lower upper : [ k ]∞} → ⦃ Eq a ⦄ → Map k a {lower} {upper} -> Map k a {lower} {upper} -> Bool

  isProperSubmapOfBy : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> Bool) -> Map k a {lower} {upper} -> Map k b {lower} {upper} -> Bool


open Submapping public
