module Data.Map.Internal.Construction where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Construction {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  empty : {lower upper : [ k ]∞} {{l≤u : lower ≤ upper}}
          → Map k a {lower} {upper}
  empty {{prf}} = Tip {{l≤u = prf}}
  {-# COMPILE AGDA2HS empty #-}

  singleton : (kx : k) → a → {lower upper : [ k ]∞} {{l≤k : lower ≤ [ kx ]}} {{k≤r : [ kx ] ≤ upper}}
          → Map k a {lower} {upper}
  singleton k x {{l≤k}} {{k≤r}} = Bin 1 k x (Tip {{l≤u = l≤k}}) (Tip {{l≤u = k≤r}})
  {-# COMPILE AGDA2HS singleton #-}

open Construction public
