module Data.Sett.Internal where

open import Haskell.Prelude
    hiding (lookup; map; filter; foldr; foldl; null; splitAt; take; drop)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup, map, filter, foldr, foldl, null, splitAt, take, drop)
#-}

data Sett (a : Set) : Set  where
  Bin : (size : Int) {_ : IsNonNegativeInt size} → (v : a) → (l : Sett a) → (r : Sett a) → Sett a
  Tip : Sett a
{-# COMPILE AGDA2HS Sett #-}

splitMember : {a : Set} → ⦃ Ord a ⦄ → a → Sett a → (Sett a × Bool × Sett a)
splitMember _ _ = (Tip , true , Tip) -- !! PLACEHOLDER !!
