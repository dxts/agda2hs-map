module Data.Map.Internal.Folding where

open import Haskell.Prelude
    hiding (foldr; foldl)
{-# FOREIGN AGDA2HS
import Prelude hiding (foldr, foldl)
#-}


open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

module Folding {k a : Set} ⦃ iOrdk : Ord k ⦄ where


  foldr : {b : Set} → (a -> b -> b) -> b -> Map k a -> b
  foldr {b} f z = go z
    where
      go : b → Map k a → b
      go z' Tip             = z'
      go z' (Bin _ _ x l r) = go (f x (go z' r)) l
  {-# COMPILE AGDA2HS foldr #-}

  foldr' : {b : Set} → (a -> b -> b) -> b -> Map k a -> b
  foldr' {b} f z = go z
    where
      go : b → Map k a → b
      go z' Tip             = seq z' z'
      go z' (Bin _ _ x l r) = go (f x (go z' r)) l
  {-# COMPILE AGDA2HS foldr' #-}

  foldl : {b : Set} → (b -> a -> b) -> b -> Map k a -> b
  foldl {b} f z = go z
    where
      go : b → Map k a → b
      go z' Tip             = z'
      go z' (Bin _ _ x l r) = go (f (go z' l) x) r
  {-# COMPILE AGDA2HS foldl #-}

  foldl' : {b : Set} → (b -> a -> b) -> b -> Map k a -> b
  foldl' {b} f z = go z
    where
      go : b → Map k a → b
      go z' Tip             = seq z' z'
      go z' (Bin _ _ x l r) = go (f (go z' l) x) r
  {-# COMPILE AGDA2HS foldl' #-}

  foldrWithKey : {b : Set} → (k -> a -> b -> b) -> b -> Map k a -> b
  foldrWithKey {b} f z = go z
    where
      go : b → Map k a → b
      go z' Tip             = z'
      go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
  {-# COMPILE AGDA2HS foldrWithKey #-}

  foldrWithKey' : {b : Set} → (k -> a -> b -> b) -> b -> Map k a -> b
  foldrWithKey' {b} f z = go z
    where
      go : b → Map k a → b
      go z' Tip             = seq z' z'
      go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
  {-# COMPILE AGDA2HS foldrWithKey' #-}

  foldlWithKey : {b : Set} → (a -> k -> b -> a) -> a -> Map k b -> a
  foldlWithKey {b} f z = go z
    where
      go : a → Map k b → a
      go z' Tip              = z'
      go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
  {-# COMPILE AGDA2HS foldlWithKey #-}

  foldlWithKey' : {b : Set} → (a -> k -> b -> a) -> a -> Map k b -> a
  foldlWithKey' {b} f z = go z
    where
      go : a → Map k b → a
      go z' Tip              = seq z' z'
      go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
  {-# COMPILE AGDA2HS foldlWithKey' #-}

  foldMapWithKey : {m : Set} → ⦃ Monoid m ⦄ -> (k -> a -> m) -> Map k a -> m
  foldMapWithKey {m} f = go
    where
      go : Map k a -> m
      go Tip             = mempty
      go (Bin sz k v l r) =
        if sz == 1
        then (f k v)
        else (mappend (go l) (mappend (f k v) (go r)))
  {-# COMPILE AGDA2HS foldMapWithKey #-}



open Folding public
