module Data.Map.Internal.Differences where

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


module Differences {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  difference : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k a {lower} {upper}

  withoutKeys : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Sett k → Map k a {lower} {upper}

  -- differenceWith : ∀ {lower upper : [ k ]∞} → (a → b → Maybe a) → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k a {lower} {upper}

  -- differenceWithKey : ∀ {lower upper : [ k ]∞} → (k → a → b → Maybe a) → Map k a {lower} {upper} → Map k b {lower} {upper} → Map k a {lower} {upper}


open Differences public
