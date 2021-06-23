module Data.Map.Internal.Lists where

open import Haskell.Prelude hiding (toList; foldr; foldl)
{-# FOREIGN AGDA2HS
import Prelude hiding (toList, foldr, foldl)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

import Data.Sett.Internal as Sett
{-# FOREIGN AGDA2HS
import qualified Data.Set.Internal as Sett
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

open import Data.Map.Internal.Folding
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Folding
#-}

open import Data.Map.Internal.Inserting
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Inserting
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}


private
  _divNat_ : Nat → Nat → Nat
  m divNat 0 = 0
  m divNat (suc n) = div-helper 0 n m n


module Lists {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  toAscList :  Map k a -> List (k × a)
  toAscList = foldrWithKey (λ k x xs -> (k , x) ∷ xs) []

  toDescList :  Map k a -> List (k × a)
  toDescList = foldlWithKey (λ xs k x -> (k , x) ∷ xs) []


  elems :  Map k a -> List a
  elems = foldr (_∷_) []
  {-# COMPILE AGDA2HS elems #-}

  keys  :  Map k a -> List k
  keys = foldrWithKey (λ k _ ks -> k ∷ ks) []
  {-# COMPILE AGDA2HS keys #-}

  assocs :  Map k a -> List (k × a)
  assocs m = toAscList m
  {-# COMPILE AGDA2HS assocs #-}

  keysSet :  Map k a -> Sett.Sett k
  keysSet Tip = Sett.Tip
  keysSet (Bin sz  kx _ l r) = Sett.Bin sz  kx (keysSet l) (keysSet r)
  {-# COMPILE AGDA2HS keysSet #-}

  fromSet :  (k -> a) -> Sett.Sett k -> Map k a
  fromSet _ Sett.Tip = Tip
  fromSet f (Sett.Bin sz  x l r) = let l' = (fromSet f l)
                                       r' = (fromSet f r)
                                   in Bin (size l' + size r' + 1) x (f x) l' r'
  {-# COMPILE AGDA2HS fromSet #-}


  {-# TERMINATING #-}
  fromList :  ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → List (k × a) -> Map k a
  fromList [] = Tip
  fromList ((kx , x) ∷ []) = Bin 1 kx x Tip Tip
  fromList  ((kx0 , x0) ∷ xs0) =
      if (not_ordered kx0 xs0)
      then (fromList' (Bin 1 kx0 x0 Tip Tip) xs0)
      else (go 1 (Bin 1 kx0 x0 Tip Tip) xs0)
    where
      not_ordered : k → List (k × a) → Bool
      not_ordered _ [] = false
      not_ordered kx ((ky , _) ∷ _) = kx >= ky

      fromList' : Map k a → List (k × a) → Map k a
      fromList' t0 xs = Haskell.Prelude.foldl ins t0 xs
        where
          ins : Map k a → (k × a) → Map k a
          ins t (k , x) = insert k x t

      create : Nat → List (k × a) → (Map k a) × (List (k × a)) × (List (k × a))
      create _ [] = (Tip , [] , [])
      create 1 xs@((kx , x) ∷ xss) = if (not_ordered kx xss)
              then (Bin 1 kx x Tip Tip , [] , xss)
              else (Bin 1 kx x Tip Tip , xss , [])
      create s xs@((kx , x) ∷ xss) = case (create (s divNat 2) xs) of
                λ {
                  res@(_ , [] , _) -> res
                ; (l , ((ky , y) ∷ []) , zs) -> (insertMax ky y l , [] , zs)
                ; (l , ys@((ky , y) ∷ yss) , _) →
                  if (not_ordered ky yss)
                  then (l , [] , ys)
                  else (case create (s divNat 2) yss of
                          λ { (r , zs , ws) -> (link ky y l r , zs , ws) })
                }

      go : Nat → Map k a → List (k × a) → Map k a
      go _ t [] = t
      go _ t ((kx , x) ∷ []) = insertMax kx x t
      go s l xs@((kx , x) ∷ xss) =
          if (not_ordered kx xss)
          then (fromList' l xs)
          else (case create s xss of
                  λ {
                    (r , ys , []) -> go (s * 2) (link kx x l r) ys
                  ; (r , _ ,  ys) -> fromList' (link kx x l r) ys
                  })


  fromListWithKey :   (k -> a -> a -> a) -> List (k × a) -> Map k a
  fromListWithKey  f xs
    = Haskell.Prelude.foldl ins empty xs
    where
      ins : Map k a → (k × a) → Map k a
      ins t (k , x) = insertWithKey f k x t

  fromListWith :   (a -> a -> a) -> List (k × a) -> Map k a
  fromListWith f xs
    = fromListWithKey (λ _ x y -> f x y) xs

  toList :  Map k a -> List (k × a)
  toList = toAscList

  foldrFB :  (k -> a -> b -> b) -> b -> Map k a -> b
  foldrFB = foldrWithKey

  foldlFB :  (a -> k -> b -> a) -> a -> Map k b -> a
  foldlFB = foldlWithKey

  combineEq' : (k -> a -> a -> a) → (k × a) → List (k × a) → List (k × a)
  combineEq' _ z [] = z ∷ []
  combineEq' f z@(kz , zz) (x@(kx , xx) ∷ xs') =
    if (kx == kz)
    then (let yy = (f kx xx zz) in combineEq' f (kx , yy) xs')
    else (z ∷ combineEq' f x xs')

  combineEq :   (k -> a -> a -> a) → List (k × a) → List (k × a)
  combineEq f xs' = case xs' of
    λ {
      []        -> []
    ; (x ∷ [])  -> x ∷ []
    ; (x ∷ xx)  -> combineEq' f x xx
    }


  {-# TERMINATING #-}
  fromDistinctAscList :  List (k × a) -> Map k a
  fromDistinctAscList [] = Tip
  fromDistinctAscList  ((kx0 , x0) ∷ xs0) = go 1 (Bin 1 kx0 x0 Tip Tip) xs0
    where
      create : Nat → List (k × a) → (Map k a) × List (k × a)
      create _ [] = (Tip , [])
      create 1 xs@((kx , x) ∷ xs') = (Bin 1 kx x Tip Tip , xs')
      create s xs@(x' ∷ xs') = case create (s divNat 2) xs of
                λ {
                  res@(_ , []) -> res
                ; (l , (ky , y) ∷ ys) -> case create (s divNat 2) ys of
                    λ { (r , zs) -> (link ky y l r , zs) }
                }

      go : Nat → Map k a → List (k × a) → Map k a
      go _ t [] = t
      go s l ((kx , x) ∷ xs) = case create s xs of
        λ { (r , ys) -> let t' = link kx x l r
                      in go (s * 2) t' ys }

  {-# TERMINATING #-}
  fromDistinctDescList : List (k × a) -> Map k a
  fromDistinctDescList [] = Tip
  fromDistinctDescList  ((kx0 , x0) ∷ xs0) = go 1 (Bin 1 kx0 x0 Tip Tip) xs0
    where
      create : Nat → List (k × a) → (Map k a) × List (k × a)
      create _ [] = (Tip , [])
      create 1 xs@((kx , x) ∷ xs') = (Bin 1 kx x Tip Tip , xs')
      create s xs@(x' ∷ xs') = case create (s divNat 2) xs of
                λ {
                  res@(_ , []) -> res
                ; (r , (ky , y) ∷ ys) -> case create (s divNat 2) ys of
                    λ { (l , zs) -> (link ky y l r , zs) }
                }

      go : Nat → Map k a → List (k × a) → Map k a
      go _ t [] = t
      go s r ((kx , x) ∷ xs) = case create s xs of
        λ { (l , ys) -> let t' = link kx x l r
                      in go (s * 2) t' ys }

  fromAscListWithKey :   (k -> a -> a -> a) -> List (k × a) -> Map k a
  fromAscListWithKey f xs
    = fromDistinctAscList (combineEq f xs)

  fromDescListWithKey :   (k -> a -> a -> a) -> List (k × a) -> Map k a
  fromDescListWithKey f xs
    = fromDistinctDescList (combineEq f xs)

  fromAscListWith :   (a -> a -> a) -> List (k × a) -> Map k a
  fromAscListWith f xs
    = fromAscListWithKey (λ _ x y -> f x y) xs

  fromDescListWith :   (a -> a -> a) -> List (k × a) -> Map k a
  fromDescListWith f xs
    = fromDescListWithKey (λ _ x y -> f x y) xs

  fromAscList :   List (k × a) -> Map k a
  fromAscList  xs = fromDistinctAscList (combineEq (λ _ x _ → x) xs)

  fromDescList :   List (k × a) -> Map k a
  fromDescList  xs = fromDistinctDescList (combineEq (λ _ x _ → x) xs)


open Lists public
