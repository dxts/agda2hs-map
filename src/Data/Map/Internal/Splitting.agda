module Data.Map.Internal.Splitting where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

module Splitting {k a : Set} ⦃ iOrdk : Ord k ⦄ where


  split :  k → Map k a → (Map k a × Map k a)
  split k Tip = Tip , Tip
  split k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT -> case (split k l) of (λ { (lt , gt) → lt , link kx x gt r})
      ; GT -> case (split k r) of (λ { (lt , gt) → link kx x l lt , gt})
      ; EQ -> (l , r)
      }
  {-# COMPILE AGDA2HS split #-}

  splitLookup :  k → Map k a → (Map k a × Maybe a × Map k a)
  splitLookup k Tip = Tip , Nothing , Tip
  splitLookup k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT -> case (splitLookup k l) of (λ { (lt , z , gt) → lt , z , link kx x gt r })
      ; GT -> case (splitLookup k r) of (λ { (lt , z , gt) → link kx x l lt , z , gt })
      ; EQ -> l , (Just x) , r
      }
  {-# COMPILE AGDA2HS splitLookup #-}

  splitMember :  k → Map k a → (Map k a × Bool × Map k a)
  splitMember k Tip = Tip , false , Tip
  splitMember k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT -> case (splitMember k l) of (λ { (lt , z , gt) → lt , z , link kx x gt r })
      ; GT -> case (splitMember k r) of (λ { (lt , z , gt) → link kx x l lt , z , gt })
      ; EQ -> l , true , r
      }
  {-# COMPILE AGDA2HS splitMember #-}

  splitRoot : Map k a → List (Map k a)
  splitRoot orig = case orig of
    λ {
      Tip             -> []
    ; (Bin _ k v l r) -> l ∷ (singleton k v) ∷ r ∷ []
    }
  {-# COMPILE AGDA2HS splitRoot #-}

open Splitting public
