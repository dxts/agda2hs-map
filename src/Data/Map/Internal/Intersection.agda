module Data.Map.Internal.Intersection where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

import Data.Sett.Internal as Sett
{-# FOREIGN AGDA2HS
import qualified Data.Set.Internal as Sett
#-}
open import Data.Sett.Internal using (Sett)
{-# FOREIGN AGDA2HS
import Data.Set.Internal (Set)
#-}

module Intersection {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  intersection : {b : Set} → ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k a {lower} {upper}

  restrictKeys : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Sett k → Map k a {lower} {upper}

  intersectionWith : {b c : Set} → ∀ {lower upper : [ k ]∞} → (a → b → c) → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k c {lower} {upper}

  intersectionWithKey : {b c : Set} → ∀ {lower upper : [ k ]∞} → (k → a → b → c) → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k c {lower} {upper}

  disjoint : {b : Set} → ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k b {lower} {upper} → Bool


open Intersection public
