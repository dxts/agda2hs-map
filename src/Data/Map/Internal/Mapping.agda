module Data.Map.Internal.Mapping where

open import Haskell.Prelude hiding (map)
{-# FOREIGN AGDA2HS
import Prelude hiding (map)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Utils.Applicative
{-# FOREIGN AGDA2HS
import Control.Applicative (liftA3)
#-}

open import Data.Map.Internal.Lists
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Lists
#-}

open import Data.Map.Internal.Folding
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Folding
#-}

open import Data.Map.PreconditionProofs


module Mapping {k a : Set} ⦃ iOrdk : Ord k ⦄ where


  map : {b : Set} -> (a -> b) -> Map k a -> Map k b
  map f Tip = Tip
  map f (Bin sz kx x l r) = Bin sz kx (f x) (map f l) (map f r)
  {-# COMPILE AGDA2HS map #-}

  mapWithKey : {b : Set} -> (k -> a -> b) -> Map k a -> Map k b
  mapWithKey _ Tip = Tip
  mapWithKey f (Bin _ kx x l r) = bin kx (f kx x) (mapWithKey f l) (mapWithKey f r)
  {-# COMPILE AGDA2HS mapWithKey #-}

  traverseWithKey : {b : Set} -> {t : Set → Set} → ⦃ Applicative t ⦄ → (k -> a -> t b) -> Map k a -> t (Map k b)
  traverseWithKey f Tip = pure Tip
  traverseWithKey f (Bin sz k v l r) = liftA3 (flip (Bin sz k)) (traverseWithKey f l) (f k v) (traverseWithKey f r)
  {-# COMPILE AGDA2HS traverseWithKey #-}


  mapAccumL : {b c : Set} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
  mapAccumL _ a Tip               = (a , Tip)
  mapAccumL f a (Bin _ kx x l r) = (a3 , bin kx x' l' r')
    where
      p1 = mapAccumL f a l
      a1 = fst p1
      l' = snd p1
      p2 = f a1 kx x
      a2 = fst p2
      x' = snd p2
      p3 = mapAccumL f a2 r
      a3 = fst p3
      r' = snd p3
  {-# COMPILE AGDA2HS mapAccumL #-}

  mapAccumWithKey : {b c : Set} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
  mapAccumWithKey f a t = mapAccumL f a t
  {-# COMPILE AGDA2HS mapAccumWithKey #-}

  mapAccum : {b c : Set} → (a -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
  mapAccum f a m = mapAccumWithKey (λ a' _ x' -> f a' x') a m
  {-# COMPILE AGDA2HS mapAccum #-}


  mapAccumRWithKey : {b c : Set} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
  mapAccumRWithKey _ a Tip = (a , Tip)
  mapAccumRWithKey f a (Bin _ kx x l r) = (a3 , bin kx x' l' r')
    where
      p1 = mapAccumRWithKey f a r
      a1 = fst p1
      r' = snd p1
      p2 = f a1 kx x
      a2 = fst p2
      x' = snd p2
      p3 = mapAccumRWithKey f a2 l
      a3 = fst p3
      l' = snd p3
  {-# COMPILE AGDA2HS mapAccumRWithKey #-}

  mapKeys : {k2 : Set} → ⦃ _ : Ord k2 ⦄ {{_ : Eq a}} {{_ : Eq (Map k2 a)}} -> (k -> k2) -> Map k a -> Map k2 a
  mapKeys f t = fromList $ foldrWithKey (λ k x xs -> (f k , x) ∷ xs) [] t
  {-# COMPILE AGDA2HS mapKeys #-}

  mapKeysWith : {k2 : Set} → ⦃ Ord k2 ⦄ -> (a -> a -> a) -> (k -> k2) -> Map k a -> Map k2 a
  mapKeysWith c f t = (fromListWith c) $ foldrWithKey (\k x xs -> (f k , x) ∷ xs) [] t
  {-# COMPILE AGDA2HS mapKeysWith #-}

  mapKeysMonotonic : {k2 : Set} → (k -> k2) -> Map k a -> Map k2 a
  mapKeysMonotonic _ Tip = Tip
  mapKeysMonotonic f (Bin _ k x l r) =
      bin (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)
  {-# COMPILE AGDA2HS mapKeysMonotonic #-}

open Mapping public
