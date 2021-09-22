module Data.Map'.Query where

open import Haskell.Prelude
    hiding (lookup; map; null)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup, map, null)
#-}

open import Data.Map'.Datatype
{-# FOREIGN AGDA2HS
import Data.Map'.Datatype
#-}

module Query {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  null : ∀ {lower upper : [ k ]∞}
        → Map k a {lower} {upper} → Bool
  null Tip = true
  null (Bin _ _ _ _ _) = false
  {-# COMPILE AGDA2HS null #-}

  lookup : ∀ {lower upper : [ k ]∞}
           → k → Map k a {lower} {upper} → Maybe a
  lookup k Tip = Nothing
  lookup k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT → lookup k l
      ; GT → lookup k r
      ; EQ → Just x
      }
  {-# COMPILE AGDA2HS lookup #-}

  member : ∀ {lower upper : [ k ]∞}
            → k → Map k a {lower} {upper} → Bool
  member _ Tip = false
  member k (Bin _ kx _ l r) = case (compare k kx) of
      λ {
        LT → member k l
      ; GT → member k r
      ; EQ → true
      }
  {-# COMPILE AGDA2HS member #-}

  notMember : ∀ {lower upper : [ k ]∞}
              → k → Map k a {lower} {upper} → Bool
  notMember k m = not (member k m)
  {-# COMPILE AGDA2HS notMember #-}

  findWithDefault : ∀ {lower upper : [ k ]∞}
                    → a → k → Map k a {lower} {upper} → a
  findWithDefault def _ Tip               = def
  findWithDefault def k (Bin _ kx x l r)  = case (compare k kx) of
      λ {
        LT → findWithDefault def k l
      ; GT → findWithDefault def k r
      ; EQ → x
      }
  {-# COMPILE AGDA2HS findWithDefault #-}

  lookupLT : ∀ {lower upper : [ k ]∞}
            → k → Map k a {lower} {upper} → Maybe (k × a)
  lookupLT _ Tip              = Nothing
  lookupLT k (Bin _ kx x l r) = if k <= kx then (lookupLT k l)
                                           else (goJust k kx x r)
    where
      goJust : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
              → k → k → a → Map k a {lower} {upper} → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust k kx' x' (Bin _ kx x l r)  = if k <= kx then (goJust k kx' x' l)
                                                     else (goJust k kx x r)
  {-# COMPILE AGDA2HS lookupLT #-}

  lookupGT : ∀ {lower upper : [ k ]∞}
            → k → Map k a {lower} {upper} → Maybe (k × a)
  lookupGT _ Tip              = Nothing
  lookupGT k (Bin _ kx x l r) = if k < kx then (goJust k kx x l)
                                          else (lookupGT k r)
    where
      goJust : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
              → k → k → a → Map k a {lower} {upper} → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust k kx' x' (Bin _ kx x l r)  = if k < kx then (goJust k kx x l)
                                                    else (goJust k kx' x' r)
  {-# COMPILE AGDA2HS lookupGT #-}

  lookupLE : ∀ {lower upper : [ k ]∞}
            → k → Map k a {lower} {upper} → Maybe (k × a)
  lookupLE _ Tip              = Nothing
  lookupLE k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT → lookupLE k l
      ; EQ → Just (kx , x)
      ; GT → goJust k kx x r
      }
    where
      goJust : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
           → k → k → a → Map k a {lower} {upper} → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust k kx' x' (Bin _ kx x l r)  = case (compare k kx) of
          λ {
            LT → goJust k kx' x' l
          ; EQ → Just (kx , x)
          ; GT → goJust k kx x r
          }
  {-# COMPILE AGDA2HS lookupLE #-}

  lookupGE : ∀ {lower upper : [ k ]∞}
             → k → Map k a {lower} {upper} → Maybe (k × a)
  lookupGE _ Tip              = Nothing
  lookupGE k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT → goJust k kx x l
      ; EQ → Just (kx , x)
      ; GT → lookupGE k r
      }
    where
      goJust : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
               → k → k → a → Map k a {lower} {upper} → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust k kx' x' (Bin _ kx x l r)  = case (compare k kx) of
          λ {
            LT → goJust k kx x l
          ; EQ → Just (kx , x)
          ; GT → goJust k kx' x' r
          }
  {-# COMPILE AGDA2HS lookupGE #-}

open Query public
