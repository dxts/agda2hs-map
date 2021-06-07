module Data.Map.Internal.Intersection where

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

open import Data.Map.Internal.Query
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Query
#-}

open import Data.Map.Internal.Splitting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Splitting
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

module Intersection {k a : Set} ⦃ iOrdk : Ord k ⦄ where


  intersection : {b : Set} -> Map k a -> Map k b -> Map k a
  intersection Tip _ = Tip
  intersection _ Tip = Tip
  intersection t1@(Bin _ k x l1 r1) t2 = case (splitMember k t2) of
      λ {
        (l2 , mb , r2) → let l1l2 = intersection l1 l2
                             r1r2 = intersection r1 r2
                          in if mb
                             then (link k x l1l2 r1r2)
                             else (link2 l1l2 r1r2)
      }
  {-# COMPILE AGDA2HS intersection #-}

  restrictKeys : Map k a -> Sett.Sett k -> Map k a
  restrictKeys Tip _ = Tip
  restrictKeys _ Sett.Tip = Tip
  restrictKeys m@(Bin _ k x l1 r1) s = case (Sett.splitMember k s) of
      λ {
        (l2 , b , r2) → let l1l2 = restrictKeys l1 l2
                            r1r2 = restrictKeys r1 r2
                          in if b
                             then (link k x l1l2 r1r2)
                             else (link2 l1l2 r1r2)
      }
  {-# COMPILE AGDA2HS restrictKeys #-}

  intersectionWith : {b c : Set} → (a -> b -> c) -> Map k a -> Map k b -> Map k c
  intersectionWith _ Tip _ = Tip
  intersectionWith _ _ Tip = Tip
  intersectionWith f (Bin _ k x1 l1 r1) t2 = case (splitLookup k t2) of
      λ {
        (l2 , mb , r2) → let l1l2 = intersectionWith f l1 l2
                             r1r2 = intersectionWith f r1 r2
                          in case mb of
                              λ {
                                (Just x2) → link k (f x1 x2) l1l2 r1r2
                              ; Nothing → link2 l1l2 r1r2
                              }
      }
  {-# COMPILE AGDA2HS intersectionWith #-}

  intersectionWithKey : {b c : Set} → (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c
  intersectionWithKey _ Tip _ = Tip
  intersectionWithKey _ _ Tip = Tip
  intersectionWithKey f (Bin _ k x1 l1 r1) t2 = case (splitLookup k t2) of
      λ {
        (l2 , mb , r2) → let l1l2 = intersectionWithKey f l1 l2
                             r1r2 = intersectionWithKey f r1 r2
                          in case mb of
                              λ {
                                (Just x2) → link k (f k x1 x2) l1l2 r1r2
                              ; Nothing → link2 l1l2 r1r2
                              }
      }
  {-# COMPILE AGDA2HS intersectionWithKey #-}

  disjoint : {b : Set} → Map k a → Map k b → Bool
  disjoint Tip _ = true
  disjoint _ Tip = true
  disjoint (Bin sz k _ l r) t =
      if (sz == 1)
      then (notMember k t)
      else case (splitMember k t) of
          λ {
            (lt , found , gt) → not found && disjoint l lt && disjoint r gt
          }
  {-# COMPILE AGDA2HS disjoint #-}

open Intersection public
