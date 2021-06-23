module Data.Map.Internal.Merging where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Splitting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Splitting
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

open import Data.Map.PreconditionProofs


module Merging {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  -- [TODO] `merge` function and it's helpers.

  mergeWithKey : {b c : Set} → ⦃ Ord b ⦄ → (k → a → b → Maybe c)
               → (Map k a → Map k c) → (Map k b → Map k c)
               → Map k a → Map k b → Map k c
  mergeWithKey {b} {c} f g1 g2 = go
    where
      go : Map k a → Map k b → Map k c
      go Tip t2 = g2 t2
      go t1@(Bin _ _ _ _ _) Tip = g1 t1
      go (Bin _ kx x l1 r1) t2 = case (splitLookup kx t2) of
          λ {
            (l2 , found , r2) → let l' = (go l1 l2)
                                    r' = (go r1 r2)
                in case found of
                λ {
                  Nothing -> case (g1 (singleton kx x)) of
                      λ {
                        Tip -> link2 l' r'
                      ; (Bin _ _ x' Tip Tip) -> link kx x' l' r'
                      ; _ -> Tip
                      }
                ; (Just x2) -> case (f kx x x2) of
                    λ {
                      Nothing -> link2 l' r'
                    ; (Just x') -> link kx x' l' r'
                    }
                }
          }
  {-# COMPILE AGDA2HS mergeWithKey #-}

open Merging public
