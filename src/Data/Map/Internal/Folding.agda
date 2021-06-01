module Data.Map.Internal.Folding where

open import Haskell.Prelude
    hiding (foldr; foldl)
{-# FOREIGN AGDA2HS
import Prelude hiding (foldr, foldl)
#-}


open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

module Folding {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  foldr : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> b) -> b -> Map k a {lower} {upper} -> b

  foldr' : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> b) -> b -> Map k a {lower} {upper} -> b

  foldl : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> a) -> a -> Map k b {lower} {upper} -> a

  foldl' : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> b -> a) -> a -> Map k b {lower} {upper} -> a

  foldrWithKey : {b : Set} → ∀ {lower upper : [ k ]∞} → (k -> a -> b -> b) -> b -> Map k a {lower} {upper} -> b

  foldrWithKey' : {b : Set} → ∀ {lower upper : [ k ]∞} → (k -> a -> b -> b) -> b -> Map k a {lower} {upper} -> b

  foldlWithKey : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> k -> b -> a) -> a -> Map k b {lower} {upper} -> a

  foldlWithKey' : {b : Set} → ∀ {lower upper : [ k ]∞} → (a -> k -> b -> a) -> a -> Map k b {lower} {upper} -> a

  foldMapWithKey : {m : Set} ⦃ _ : Monoid m ⦄ -> ∀ {lower upper : [ k ]∞} → (k -> a -> m) -> Map k a {lower} {upper} -> m


open Folding public
