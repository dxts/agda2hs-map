module Data.Map.Internal.Query where

open import Haskell.Prelude
    hiding (lookup; map; null)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup, map, null)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.PreconditionProofs

module Query {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  null : Map k a → Bool
  null Tip = true
  null (Bin _ _ _ _ _) = false
  {-# COMPILE AGDA2HS null #-}

  lookup :  k → Map k a → Maybe a
  lookup k Tip = Nothing
  lookup k (Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT → lookup k l
      ; GT → lookup k r
      ; EQ → Just x
      }
  {-# COMPILE AGDA2HS lookup #-}

  member :  k → Map k a → Bool
  member _ Tip = false
  member k (Bin _ kx _ l r) = case (compare k kx) of
      λ {
        LT → member k l
      ; GT → member k r
      ; EQ → true
      }
  {-# COMPILE AGDA2HS member #-}

  notMember :  k → Map k a → Bool
  notMember k m = not (member k m)
  {-# COMPILE AGDA2HS notMember #-}

  find :  (key : k) (map : Map k a) → {key ∈ map} → a
  find key t@(Bin sz kx x l r {szVal}) {prf} = match (compare {{iOrdk}} key kx) {refl}
    where
      match : (o : Ordering) → {eq : compare {{iOrdk}} key kx ≡ o} → a
      match LT {eq} = find key l {∈L sz key kx x l r szVal eq prf}
      match GT {eq} = find key r {∈R sz key kx x l r szVal eq prf}
      match EQ {eq} = x
  {-# COMPILE AGDA2HS find #-}

  findWithDefault :  a → k → Map k a → a
  findWithDefault def _ Tip               = def
  findWithDefault def k (Bin _ kx x l r)  = case (compare k kx) of
      λ {
        LT → findWithDefault def k l
      ; GT → findWithDefault def k r
      ; EQ → x
      }
  {-# COMPILE AGDA2HS findWithDefault #-}

  lookupLT :  k → Map k a → Maybe (k × a)
  lookupLT _ Tip              = Nothing
  lookupLT k (Bin _ kx x l r) = if k <= kx then (lookupLT k l)
                                           else (goJust k kx x r)
    where
      goJust : {k a : Set} →  ⦃ _ : Ord k ⦄
              → k → k → a → Map k a → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust k kx' x' (Bin _ kx x l r)  = if k <= kx then (goJust k kx' x' l)
                                                     else (goJust k kx x r)
  {-# COMPILE AGDA2HS lookupLT #-}

  lookupGT :  k → Map k a → Maybe (k × a)
  lookupGT _ Tip              = Nothing
  lookupGT k (Bin _ kx x l r) = if k < kx then (goJust k kx x l)
                                          else (lookupGT k r)
    where
      goJust : {k a : Set} →  ⦃ _ : Ord k ⦄
              → k → k → a → Map k a → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust k kx' x' (Bin _ kx x l r)  = if k < kx then (goJust k kx x l)
                                                    else (goJust k kx' x' r)
  {-# COMPILE AGDA2HS lookupGT #-}

  lookupLE : k → Map k a → Maybe (k × a)
  lookupLE _ Tip              = Nothing
  lookupLE key (Bin _ kx x l r) = match1 (compare key kx)
    where
      goJust : k → k → a → Map k a → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust key kx' x' (Bin _ kx x l r)  = match2 (compare key kx)
        where
          match2 : Ordering → Maybe (k × a)
          match2 LT = goJust key kx' x' l
          match2 GT = Just (kx , x)
          match2 EQ = goJust key kx x r

      match1 : Ordering → Maybe (k × a)
      match1 LT = lookupLE key l
      match1 GT = Just (kx , x)
      match1 EQ = goJust key kx x r
  {-# COMPILE AGDA2HS lookupLE #-}

  lookupGE :  k → Map k a → Maybe (k × a)
  lookupGE _ Tip              = Nothing
  lookupGE key (Bin _ kx x l r) = match1 (compare key kx)
    where
      goJust : k → k → a → Map k a → Maybe (k × a)
      goJust _ kx' x' Tip               = Just (kx' , x')
      goJust key kx' x' (Bin _ kx x l r)  = match2 (compare key kx)
        where
          match2 : Ordering → Maybe (k × a)
          match2 LT = goJust key kx x l
          match2 EQ = Just (kx , x)
          match2 GT = lookupGE key r

      match1 : Ordering → Maybe (k × a)
      match1 LT = lookupLE key l
      match1 GT = Just (kx , x)
      match1 EQ = goJust key kx x r
  {-# COMPILE AGDA2HS lookupGE #-}

open Query public
