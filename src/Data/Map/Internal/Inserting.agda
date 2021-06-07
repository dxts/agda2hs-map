module Data.Map.Internal.Inserting where

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

open import Data.Map.Internal.Balancing
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Balancing
#-}

module Inserting {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  insert :  ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
  insert kx x Tip                 = singleton kx x
  insert kx x t@(Bin sz ky y l r {szVal}) = case (compare kx ky) of
      λ {
        LT → let l' = insert kx x l in if (l' == l) then t else (balanceL ky y l' r)
      ; GT → let r' = insert kx x r in if (r' == r) then t else (balanceR ky y l r')
      ; EQ → if (x == y && kx == ky) then t else (Bin sz kx x l r {szVal})
      }
  {-# COMPILE AGDA2HS insert #-}

  insertR :  ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
  insertR kx x Tip                 = singleton kx x
  insertR kx x t@(Bin sz ky y l r) = case (compare kx ky) of
      λ {
        LT → let l' = insert kx x l in if (l' == l) then t else (balanceL ky y l' r)
      ; GT → let r' = insert kx x r in if (r' == r) then t else (balanceR ky y l r')
      ; EQ → t
      }
  {-# COMPILE AGDA2HS insertR #-}

  insertWith :  (a → a → a) → k → a → Map k a → Map k a
  insertWith _ kx x Tip               = singleton kx x
  insertWith f kx x (Bin sz ky y l r {szVal}) = case (compare kx ky) of
      λ {
        LT → balanceL ky y (insertWith f kx x l) r
      ; GT → balanceR ky y l (insertWith f kx x r)
      ; EQ → Bin sz kx (f x y) l r {szVal}
      }
  {-# COMPILE AGDA2HS insertWith #-}

  insertWithR :  (a → a → a) → k → a → Map k a → Map k a
  insertWithR _ kx x Tip               = singleton kx x
  insertWithR f kx x (Bin sz ky y l r {szVal}) = case (compare kx ky) of
      λ {
        LT → balanceL ky y (insertWith f kx x l) r
      ; GT → balanceR ky y l (insertWith f kx x r)
      ; EQ → Bin sz kx (f y x) l r {szVal}
      }
  {-# COMPILE AGDA2HS insertWithR #-}

  insertWithKey :  (k → a → a → a) → k → a → Map k a → Map k a
  insertWithKey _ kx x Tip                = singleton kx x
  insertWithKey f kx x (Bin sz ky y l r {szVal})  = case (compare kx ky) of
      λ {
        LT → balanceL ky y (insertWithKey f kx x l) r
      ; GT → balanceR ky y l (insertWithKey f kx x r)
      ; EQ → Bin sz kx (f kx x y) l r {szVal}
      }
  {-# COMPILE AGDA2HS insertWithKey #-}

  insertWithKeyR :  (k → a → a → a) → k → a → Map k a → Map k a
  insertWithKeyR _ kx x Tip                = singleton kx x
  insertWithKeyR f kx x (Bin sz ky y l r {szVal})  = case (compare kx ky) of
      λ {
        LT → balanceL ky y (insertWithKey f kx x l) r
      ; GT → balanceR ky y l (insertWithKey f kx x r)
      ; EQ → Bin sz kx (f kx y x) l r {szVal}
      }
  {-# COMPILE AGDA2HS insertWithKeyR #-}

  insertLookupWithKey :  (k → a → a → a) → k → a → Map k a → (Maybe a × Map k a)
  insertLookupWithKey _ kx x Tip                = (Nothing , singleton kx x)
  insertLookupWithKey f kx x (Bin sz ky y l r {szVal})  = case (compare kx ky) of
      λ {
        LT → let res = insertLookupWithKey f kx x l
                 t' = balanceL ky y (snd res) r
                 in (fst res , t')
      ; GT → let res = insertLookupWithKey f kx x r
                 t' = balanceR ky y l (snd res)
                 in (fst res , t')
      ; EQ → (Just y , Bin sz kx (f kx x y) l r {szVal})
      }
  {-# COMPILE AGDA2HS insertLookupWithKey #-}



open Inserting public
