module Data.Map.Internal.Unions where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

open import Data.Map.Internal.Inserting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Inserting
#-}

open import Data.Map.Internal.Splitting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Splitting
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

open import Data.Map.PreconditionProofs

module Unions {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  -- [TODO] Note : check usage of Foldable.foldl vs Haskell.Prelude.foldl

  union : ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → Map k a → Map k a → Map k a
  union t1 Tip  = t1
  union t1 (Bin _ k x Tip Tip) = insertR k x t1
  union (Bin _ k x Tip Tip) t2 = insert k x t2
  union Tip t2 = t2
  union t1@(Bin _ k1 x1 l1 r1) t2 = case (split k1 t2) of
      λ {
        (l2 , r2) → let l1l2 = union l1 l2
                        r1r2 = union r1 r2
                      in link k1 x1 l1l2 r1r2
      }
  {-# COMPILE AGDA2HS union #-}

  unions : ⦃ Foldable f ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → f (Map k a) → Map k a
  unions ts = Haskell.Prelude.foldl union empty ts
  {-# COMPILE AGDA2HS unions #-}


  unionWith : (a → a → a) → Map k a → Map k a → Map k a
  unionWith _f t1 Tip = t1
  unionWith f t1 (Bin _ k x Tip Tip) = insertWithR f k x t1
  unionWith f (Bin _ k x Tip Tip) t2 = insertWith f k x t2
  unionWith _f Tip t2 = t2
  unionWith f (Bin _ k1 x1 l1 r1) t2 = case (splitLookup k1 t2) of
      λ {
        (l2 , mb , r2) → let l1l2 = unionWith f l1 l2
                             r1r2 = unionWith f r1 r2
                            in case mb of
            λ {
              Nothing → link k1 x1 l1l2 r1r2
            ; (Just x2) → link k1 (f x1 x2) l1l2 r1r2
            }
      }
  {-# COMPILE AGDA2HS unionWith #-}

  unionsWith : ⦃ Foldable f ⦄ → (a → a → a) → f (Map k a) → Map k a
  unionsWith f ts = Haskell.Prelude.foldl (unionWith f) empty ts
  {-# COMPILE AGDA2HS unionsWith #-}


  unionWithKey : (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a
  unionWithKey _ t1 Tip = t1
  unionWithKey f t1 (Bin _ k x Tip Tip) = insertWithKeyR f k x t1
  unionWithKey f (Bin _ k x Tip Tip) t2 = insertWithKey f k x t2
  unionWithKey _ Tip t2 = t2
  unionWithKey f (Bin _ k1 x1 l1 r1) t2 = case (splitLookup k1 t2) of
      λ {
        (l2 , mb , r2) -> let l1l2 = unionWithKey f l1 l2
                              r1r2 = unionWithKey f r1 r2
                            in case mb of
            λ {
              Nothing -> link k1 x1 l1l2 r1r2
            ; (Just x2) -> link k1 (f k1 x1 x2) l1l2 r1r2
            }
      }
  {-# COMPILE AGDA2HS unionWithKey #-}

open Unions public
