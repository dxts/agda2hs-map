module Data.Map.Internal.MinMax where

open import Haskell.Prelude hiding (null)
{-# FOREIGN AGDA2HS
import Prelude hiding (null)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Query
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Query
#-}

open import Data.Map.Internal.Balancing
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Balancing
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

module MinMax {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  lookupMinSure : k → a → Map k a → k × a
  lookupMinSure k a Tip = (k , a)
  lookupMinSure _ _ (Bin _ kx x l _) = lookupMinSure kx x l
  {-# COMPILE AGDA2HS lookupMinSure #-}

  lookupMin : Map k a → Maybe (k × a)
  lookupMin Tip = Nothing
  lookupMin (Bin _ kx x l _) = Just $! lookupMinSure kx x l
  {-# COMPILE AGDA2HS lookupMin #-}

  findMin : (map : Map k a) → {IsTrue (not (null map))} → k × a
  findMin Tip = error "Map.findMin: empty map has no minimal element"
  findMin (Bin _ kx x l _) = lookupMinSure kx x l
  {-# COMPILE AGDA2HS findMin #-}

  lookupMaxSure : k → a → Map k a → k × a
  lookupMaxSure k a Tip = (k , a)
  lookupMaxSure _ _ (Bin _ kx x _ r) = lookupMaxSure kx x r
  {-# COMPILE AGDA2HS lookupMaxSure #-}

  lookupMax : Map k a → Maybe (k × a)
  lookupMax Tip = Nothing
  lookupMax (Bin _ kx x _ r) = Just $! lookupMaxSure kx x r
  {-# COMPILE AGDA2HS lookupMax #-}

  findMax : (map : Map k a) → {IsTrue (not (null map))} → k × a
  findMax Tip = error "Map.findMax: empty map has no maximal element"
  findMax (Bin _ kx x _ r) = lookupMaxSure kx x r
  {-# COMPILE AGDA2HS findMax #-}

  deleteMin : Map k a → Map k a
  deleteMin (Bin _ _  _ Tip r) = r
  deleteMin (Bin _ kx x l@(Bin _ _ _ _ _) r) = balanceR kx x (deleteMin l) r
  deleteMin Tip = Tip
  {-# COMPILE AGDA2HS deleteMin #-}

  deleteMax : Map k a → Map k a
  deleteMax (Bin _ _  _ l Tip) = l
  deleteMax (Bin _ kx x l r@(Bin _ _ _ _ _)) = balanceL kx x l (deleteMax r)
  deleteMax Tip = Tip
  {-# COMPILE AGDA2HS deleteMax #-}


  updateMinWithKey : (k → a → Maybe a) → Map k a → Map k a
  updateMinWithKey _ Tip                 = Tip
  updateMinWithKey f (Bin sx kx x Tip r {szVal}) = case (f kx x) of
      λ {
        Nothing → r
      ; (Just x') → Bin sx kx x' Tip r {szVal}
      }
  updateMinWithKey f (Bin _ kx x l@(Bin _ _ _ _ _) r)    = balanceR kx x (updateMinWithKey f l) r
  {-# COMPILE AGDA2HS updateMinWithKey #-}

  updateMin : (a → Maybe a) → Map k a → Map k a
  updateMin f m = updateMinWithKey (λ _ x → f x) m
  {-# COMPILE AGDA2HS updateMin #-}


  updateMaxWithKey : (k → a → Maybe a) → Map k a → Map k a
  updateMaxWithKey _ Tip                 = Tip
  updateMaxWithKey f (Bin sx kx x l Tip {szVal}) = case (f kx x) of
      λ {
        Nothing → l
      ; (Just x') → Bin sx kx x' l Tip {szVal}
      }
  updateMaxWithKey f (Bin _ kx x l r@(Bin _ _ _ _ _))    = balanceL kx x l (updateMaxWithKey f r)
  {-# COMPILE AGDA2HS updateMaxWithKey #-}

  updateMax : (a → Maybe a) → Map k a → Map k a
  updateMax f m = updateMaxWithKey (λ _ x → f x) m
  {-# COMPILE AGDA2HS updateMax #-}


  minViewWithKey : Map k a → Maybe ((k × a) × Map k a)
  minViewWithKey Tip = Nothing
  minViewWithKey (Bin _ k x l r) = case (minViewSure k x l r) of
      λ {
        (MinViewCon km xm t) → Just ((km , xm) , t)
      }
  {-# COMPILE AGDA2HS minViewWithKey #-}

  maxViewWithKey : Map k a → Maybe ((k × a) × Map k a)
  maxViewWithKey Tip = Nothing
  maxViewWithKey (Bin _ k x l r) = case (maxViewSure k x l r) of
      λ {
        (MaxViewCon km xm t) → Just ((km , xm) , t)
      }
  {-# COMPILE AGDA2HS maxViewWithKey #-}

  minView : Map k a → Maybe (a × Map k a)
  minView t = case (minViewWithKey t) of
      λ {
        Nothing → Nothing
      ; (Just ((_ , x) , t')) → Just (x , t')
      }
  {-# COMPILE AGDA2HS minView #-}

  maxView : Map k a → Maybe (a × Map k a)
  maxView t = case (maxViewWithKey t) of
      λ {
        Nothing → Nothing
      ; (Just ((_ , x) , t')) → Just (x , t')
      }
  {-# COMPILE AGDA2HS maxView #-}

open MinMax public
