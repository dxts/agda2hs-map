module Data.Map.Internal.Lists where

open import Haskell.Prelude hiding (toList)
{-# FOREIGN AGDA2HS
import Prelude hiding (toList)
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

module Lists {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  elems : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> List a

  keys  : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> List k

  assocs : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> List (k × a)

  keysSet : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> Sett.Sett k

  fromSet : ∀ {lower upper : [ k ]∞} → (k -> a) -> Sett.Sett k -> Map k a {lower} {upper}

  fromList : ∀ {lower upper : [ k ]∞} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a {lower} {upper}) ⦄ → List (k × a) -> Map k a {lower} {upper}

  fromListWith : ∀ {lower upper : [ k ]∞} → ⦃ Ord k ⦄ → (a -> a -> a) -> List (k × a) -> Map k a {lower} {upper}

  fromListWithKey : ∀ {lower upper : [ k ]∞} → ⦃ Ord k ⦄ → (k -> a -> a -> a) -> List (k × a) -> Map k a {lower} {upper}

  toList : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> List (k × a)

  toAscList : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> List (k × a)

  toDescList : ∀ {lower upper : [ k ]∞} → Map k a {lower} {upper} -> List (k × a)

  foldrFB : ∀ {lower upper : [ k ]∞} → (k -> a -> b -> b) -> b -> Map k a {lower} {upper} -> b

  foldlFB : ∀ {lower upper : [ k ]∞} → (b -> k -> a -> b) -> b -> Map k a {lower} {upper} -> b

  fromAscList : ∀ {lower upper : [ k ]∞} → ⦃ Eq k ⦄ → List (k × a) -> Map k a {lower} {upper}

  fromDescList : ∀ {lower upper : [ k ]∞} → ⦃ Eq k ⦄ → List (k × a) -> Map k a {lower} {upper}

  fromAscListWith : ∀ {lower upper : [ k ]∞} → ⦃ Eq k ⦄ → (a -> a -> a) -> List (k × a) -> Map k a {lower} {upper}

  fromDescListWith : ∀ {lower upper : [ k ]∞} → ⦃ Eq k ⦄ → (a -> a -> a) -> List (k × a) -> Map k a {lower} {upper}

  fromAscListWithKey : ∀ {lower upper : [ k ]∞} → ⦃ Eq k ⦄ → (k -> a -> a -> a) -> List (k × a) -> Map k a {lower} {upper}

  fromDescListWithKey : ∀ {lower upper : [ k ]∞} → ⦃ Eq k ⦄ → (k -> a -> a -> a) -> List (k × a) -> Map k a {lower} {upper}

  fromDistinctAscList : ∀ {lower upper : [ k ]∞} → List (k × a) -> Map k a {lower} {upper}

  fromDistinctDescList : ∀ {lower upper : [ k ]∞} → List (k × a) -> Map k a {lower} {upper}


open Lists public
