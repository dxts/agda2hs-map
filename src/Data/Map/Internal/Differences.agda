module Data.Map.Internal.Differences where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

import Data.Sett.Internal as Sett
{-# FOREIGN AGDA2HS
import qualified Data.Set.Internal as Sett
#-}

open import Data.Map.Internal.Splitting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Splitting
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}


module Differences {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  difference :  {b : Set} → Map k a -> Map k b -> Map k a
  difference Tip _   = Tip
  difference t1@(Bin _ _ _ _ _) Tip  = t1
  difference t1@(Bin _ _ _ _ _) (Bin _ k _ l2 r2) = case (split k t1) of
      λ {
        (l1 , r1) -> let l1l2 = difference l1 l2
                         r1r2 = difference r1 r2
                      in if (size l1l2 + size r1r2 == size t1) then t1 else (link2 l1l2 r1r2)
      }
  {-# COMPILE AGDA2HS difference #-}

  withoutKeys :  Map k a -> Sett.Sett k -> Map k a
  withoutKeys Tip _ = Tip
  withoutKeys m@(Bin _ _ _ _ _) Sett.Tip = m
  withoutKeys m@(Bin _ _ _ _ _) (Sett.Bin _ k ls rs) = case (splitMember k m) of
      λ {
        (lm , b , rm) -> let lm' = withoutKeys lm ls
                             rm' = withoutKeys rm rs
                          in if (not b) then m else (link2 lm' rm')
      }
  {-# COMPILE AGDA2HS withoutKeys #-}

  -- differenceWith :  (a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
  -- [TODO]

  -- differenceWithKey :  (k -> a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
  -- [TODO]

open Differences public
