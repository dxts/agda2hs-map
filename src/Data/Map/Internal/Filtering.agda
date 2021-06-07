module Data.Map.Internal.Filtering where

open import Haskell.Prelude hiding (filter)
{-# FOREIGN AGDA2HS
import Prelude hiding (filter)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

open import Data.Utils.Applicative
{-# FOREIGN AGDA2HS
import Control.Applicative (liftA3)
#-}

module Filtering {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  mutual
    filter :  (a -> Bool) -> Map k a -> Map k a
    filter p m = filterWithKey (λ _ x -> p x) m

    filterWithKey :  (k -> a -> Bool) -> Map k a -> Map k a
    filterWithKey _ Tip = Tip
    filterWithKey p t@(Bin _ kx x l r) =
        let pl = filterWithKey p l
            pr = filterWithKey p r
        in if (p kx x)
        then (link kx x pl pr)
        else (link2 pl pr)
    {-# COMPILE AGDA2HS filterWithKey #-}

  filterWithKeyA :  {f : Set → Set} → ⦃ _ : Applicative f ⦄ → (k -> a -> f Bool) -> Map k a -> f (Map k a)
  filterWithKeyA _ Tip = pure Tip
  filterWithKeyA  p (Bin _ kx x l r) =  liftA3 combine (p kx x) (filterWithKeyA p l) (filterWithKeyA p r)
    where
      combine : Bool → Map k a → Map k a → Map k a
      combine true pl pr = link kx x pl pr
      combine false pl pr = link2 pl pr
  {-# COMPILE AGDA2HS filterWithKeyA #-}

  takeWhileAntitone :  (k -> Bool) -> Map k a -> Map k a
  takeWhileAntitone _ Tip = Tip
  takeWhileAntitone p (Bin _ kx x l r) =
      if (p kx)
      then (link kx x l (takeWhileAntitone p r))
      else (takeWhileAntitone p l)
  {-# COMPILE AGDA2HS takeWhileAntitone #-}

  dropWhileAntitone :  (k -> Bool) -> Map k a -> Map k a
  dropWhileAntitone _ Tip = Tip
  dropWhileAntitone p (Bin _ kx x l r) =
      if (p kx)
      then (dropWhileAntitone p r)
      else (link kx x (dropWhileAntitone p l) r)
  {-# COMPILE AGDA2HS dropWhileAntitone #-}

  spanAntitone :  (k -> Bool) -> Map k a -> (Map k a) × (Map k a)
  spanAntitone _ Tip = Tip , Tip
  spanAntitone p (Bin _ kx x l r) =
      if (p kx)
      then (case (spanAntitone p r) of λ { (u , v) → link kx x l u , v })
      else (case (spanAntitone p l) of λ { (u , v) → u , link kx x v r })
  {-# COMPILE AGDA2HS spanAntitone #-}


  partitionWithKey :  (k -> a -> Bool) -> Map k a -> (Map k a) × (Map k a)
  partitionWithKey _ Tip = (Tip , Tip)
  partitionWithKey p t@(Bin _ kx x l r) = let p1 = partitionWithKey p l
                                              l1 = fst p1
                                              l2 = snd p1
                                              p2 = partitionWithKey p r
                                              r1 = fst p2
                                              r2 = snd p2
      in if (p kx x)
      then (link kx x l1 r1 , link2 l2 r2)
      else (link2 l1 r1 , link kx x l2 r2)
  {-# COMPILE AGDA2HS partitionWithKey #-}

  partition :  (a -> Bool) -> Map k a -> (Map k a) × (Map k a)
  partition p m = partitionWithKey (λ _ x -> p x) m
  {-# COMPILE AGDA2HS partition #-}


  mapMaybeWithKey :  {b : Set} → (k -> a -> Maybe b) -> Map k a -> Map k b
  mapMaybeWithKey _ Tip = Tip
  mapMaybeWithKey f (Bin _ kx x l r) = case (f kx x) of
      λ {
        (Just y)  -> link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
      ; Nothing -> link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)
      }
  {-# COMPILE AGDA2HS mapMaybeWithKey #-}

  mapMaybe :  (a -> Maybe b) -> Map k a -> Map k b
  mapMaybe f = mapMaybeWithKey (λ _ x -> f x)
  {-# COMPILE AGDA2HS mapMaybe #-}


  traverseMaybeWithKey : {b : Set} → {f : Set → Set} → ⦃ Applicative f ⦄ → (k -> a -> f (Maybe b)) -> Map k a -> f (Map k b)
  traverseMaybeWithKey _ Tip = pure Tip
  traverseMaybeWithKey p (Bin _ kx x Tip Tip) = maybe Tip (λ x' -> Bin 1 kx x' Tip Tip) <$> p kx x
  traverseMaybeWithKey  {b} p (Bin _ kx x l r) = liftA3 combine (traverseMaybeWithKey p l) (p kx x) (traverseMaybeWithKey p r)
    where
      combine : Map k b → Maybe b → Map k b → Map k b
      combine l' mx r' = case mx of
          λ {
            Nothing -> link2 l' r'
          ; (Just x') -> link kx x' l' r'
          }
  {-# COMPILE AGDA2HS traverseMaybeWithKey #-}


  mapEitherWithKey : {b c : Set} → (k -> a -> Either b c) -> Map k a -> (Map k b) × (Map k c)
  mapEitherWithKey _ Tip = (Tip , Tip)
  mapEitherWithKey p (Bin _ kx x l r) = let p1 = mapEitherWithKey p l
                                            l1 = fst p1
                                            l2 = snd p1
                                            p2 = mapEitherWithKey p r
                                            r1 = fst p2
                                            r2 = snd p2
    in case (p kx x) of
      λ {
        (Left y)  -> link kx y l1 r1 , link2 l2 r2
      ; (Right z) -> link2 l1 r1 , link kx z l2 r2
      }
  {-# COMPILE AGDA2HS mapEitherWithKey #-}

  mapEither : {b c : Set} → (a -> Either b c) -> Map k a -> (Map k b) × (Map k c)
  mapEither f m = mapEitherWithKey (λ _ x -> f x) m
  {-# COMPILE AGDA2HS mapEither #-}


open Filtering public
