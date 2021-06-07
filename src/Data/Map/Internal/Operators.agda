module Data.Map.Internal.Operators where

open import Haskell.Prelude hiding (lookup)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Query
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Query
#-}

open import Data.Map.Internal.Differences
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Differences
#-}

open import Data.Map.PreconditionProofs

module Operators {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  _!_ : (map : Map k a) → (key : k) → {key ∈ map} → a
  _!_ m k {notEmpty} = find k m {notEmpty}
  {-# COMPILE AGDA2HS _!_ #-}

  _!?_ : Map k a -> k -> Maybe a
  _!?_ m k = lookup k m
  {-# COMPILE AGDA2HS _!?_ #-}

  _\\_ : Map k a -> Map k b -> Map k a
  _\\_ m1 m2 = difference m1 m2
  {-# COMPILE AGDA2HS _\\_ #-}


open Operators public
