module Data.Map.Internal.MinMax where

open import Haskell.Prelude hiding (null)
{-# FOREIGN AGDA2HS
import Prelude hiding (null)
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.Internal.Query
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Query
#-}

module MinMax {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  lookupMinSure : ∀ {lower upper : [ k ]∞} → k → a → Map k a {lower} {upper} → k × a

  lookupMin : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Maybe (k × a)

  findMin : ∀ {lower upper : [ k ]∞} → (map : Map k a {lower} {upper}) → {IsTrue (not (null map))} → k × a

  lookupMaxSure : ∀ {lower upper : [ k ]∞} → k → a → Map k a {lower} {upper} → k × a

  lookupMax : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Maybe (k × a)

  findMax : ∀ {lower upper : [ k ]∞} → (map : Map k a {lower} {upper}) → {IsTrue (not (null map))} → k × a

  deleteMin : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k a {lower} {upper}

  deleteMax : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k a {lower} {upper}

  updateMin : ∀ {lower upper : [ k ]∞} → (a → Maybe a) → Map k a {lower} {upper} → Map k a {lower} {upper}

  updateMax : ∀ {lower upper : [ k ]∞} → (a → Maybe a) → Map k a {lower} {upper} → Map k a {lower} {upper}

  updateMinWithKey : ∀ {lower upper : [ k ]∞} → (k → a → Maybe a) → Map k a {lower} {upper} → Map k a {lower} {upper}

  updateMaxWithKey : ∀ {lower upper : [ k ]∞} → (k → a → Maybe a) → Map k a {lower} {upper} → Map k a {lower} {upper}

  minViewWithKey : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Maybe ((k × a) × Map k a {lower} {upper})

  maxViewWithKey : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Maybe ((k × a) × Map k a {lower} {upper})

  minView : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Maybe (a × Map k a {lower} {upper})

  maxView : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} → Maybe (a × Map k a {lower} {upper})

open MinMax public
