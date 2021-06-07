module Data.Map.Internal.Submapping where

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

open import Data.Map.Internal.Splitting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Splitting
#-}


open import Data.Map.PreconditionProofs

module Submapping {k a : Set} ⦃ iOrdk : Ord k ⦄ where


  submap' : {b : Set} → (a -> b -> Bool) -> Map k a -> Map k b -> Bool
  submap' _ Tip _ = true
  submap' _ _ Tip = false
  submap' f (Bin sz kx x l r) t =
      if (sz == 1)
      then (case (lookup kx t) of
          λ {
            (Just y) -> f x y
          ; Nothing -> false
          })
      else (case (splitLookup kx t) of
          λ {
                (lt , found , gt) -> case found of
                    λ {
                      Nothing -> false
                    ; (Just y) -> (f x y)
                                  && (size l <= size lt) && (size r <= size gt)
                                  && (submap' f l lt) && (submap' f r gt)
                    }
          })
  {-# COMPILE AGDA2HS submap' #-}

  isSubmapOfBy : {b : Set} → (a -> b -> Bool) -> Map k a -> Map k b -> Bool
  isSubmapOfBy f t1 t2 = (size t1 <= size t2) && (submap' f t1 t2)
  {-# COMPILE AGDA2HS isSubmapOfBy #-}

  isSubmapOf : ⦃ Eq a ⦄ → Map k a -> Map k a -> Bool
  isSubmapOf m1 m2 = isSubmapOfBy (_==_) m1 m2
  {-# COMPILE AGDA2HS isSubmapOf #-}



  isProperSubmapOfBy : (a -> b -> Bool) -> Map k a -> Map k b -> Bool
  isProperSubmapOfBy f t1 t2 = (size t1 < size t2) && (submap' f t1 t2)
  {-# COMPILE AGDA2HS isProperSubmapOfBy #-}

  isProperSubmapOf : ⦃ Eq a ⦄ → Map k a -> Map k a -> Bool
  isProperSubmapOf m1 m2 = isProperSubmapOfBy (_==_) m1 m2
  {-# COMPILE AGDA2HS isProperSubmapOf #-}

open Submapping public
