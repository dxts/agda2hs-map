module Data.Map.Internal.Construction where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

module Construction {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  empty : Map k a
  empty = Tip
  {-# COMPILE AGDA2HS empty #-}

  singleton : (kx : k) → a → Map k a
  singleton k x = Bin 1 k x Tip Tip
  {-# COMPILE AGDA2HS singleton #-}

open Construction public
