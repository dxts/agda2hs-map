module Data.Map.Internal.Linking where

open import Haskell.Prelude hiding (null)
{-# FOREIGN AGDA2HS
import Prelude hiding (null)
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Query
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Query
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

open import Data.Map.Internal.Balancing
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Balancing
#-}



data MinView (k : Set) (a : Set) : Set where
  MinViewCon : k → a → (Map k a) → MinView k a
{-# COMPILE AGDA2HS MinView #-}

data MaxView (k : Set) (a : Set) : Set where
  MaxViewCon : k → a → (Map k a) → MaxView k a
{-# COMPILE AGDA2HS MaxView #-}


module Linking {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  insertMax : k → a → Map k a → Map k a
  insertMax kx x Tip = singleton kx x
  insertMax kx x (Bin _ ky y l r) = balanceR ky y l (insertMax kx x r)
  {-# COMPILE AGDA2HS insertMax #-}

  insertMin : k → a → Map k a → Map k a
  insertMin kx x Tip = singleton kx x
  insertMin kx x (Bin _ ky y l r) = balanceL ky y (insertMin kx x l) r
  {-# COMPILE AGDA2HS insertMin #-}

  link : k → a → Map k a → Map k a → Map k a
  link kx x Tip r  = insertMin kx x r
  link kx x l Tip  = insertMax kx x l
  link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz) =
    if (delta * sizeL < sizeR)
    then (balanceL kz z (link kx x l lz) rz)
    else (if (delta * sizeR < sizeL)
          then (balanceR ky y ly (link kx x ry r))
          else (bin kx x l r))
  {-# COMPILE AGDA2HS link #-}


  minViewSure : k → a → Map k a → Map k a → MinView k a
  minViewSure k x Tip r                 = MinViewCon k x r
  minViewSure k x (Bin _ kl xl ll lr) r = case (minViewSure kl xl ll lr) of
      λ {
        (MinViewCon km xm l') → MinViewCon km xm (balanceR k x l' r)
      }
  {-# COMPILE AGDA2HS minViewSure #-}

  maxViewSure : k → a → Map k a → Map k a → MaxView k a
  maxViewSure k x l Tip                 = MaxViewCon k x l
  maxViewSure k x l (Bin _ kr xr rl rr) = case (maxViewSure kr xr rl rr) of
      λ {
        (MaxViewCon km xm r') → MaxViewCon km xm (balanceL k x l r')
      }
  {-# COMPILE AGDA2HS maxViewSure #-}

  deleteFindMin : (map : Map k a) → {IsTrue (not (null map))} → ((k × a) × Map k a)
  deleteFindMin Tip = (error "Map.deleteFindMin: can not return the minimal element of an empty map" , Tip)
  deleteFindMin t@(Bin _ k x l r) = case (minViewSure k x l r) of
      λ {
        (MinViewCon km xm t) → ((km , xm) , t)
      }
  {-# COMPILE AGDA2HS deleteFindMin #-}

  deleteFindMax : (map : Map k a) → {IsTrue (not (null map))} → ((k × a) × Map k a)
  deleteFindMax Tip = (error "Map.deleteFindMax: can not return the maximal element of an empty map" , Tip)
  deleteFindMax t@(Bin _ k x l r) = case (maxViewSure k x l r) of
      λ {
        (MaxViewCon km xm t) → ((km , xm) , t)
      }
  {-# COMPILE AGDA2HS deleteFindMax #-}


  glue : Map k a → Map k a → Map k a
  glue Tip r = r
  glue l@(Bin _ _ _ _ _) Tip = l
  glue l@(Bin sl kl xl ll lr) r@(Bin sr kr xr rl rr) = if (sl > sr)
                                                       then (case (maxViewSure kl xl ll lr) of λ { (MaxViewCon km m l') → balanceR km m l' r})
                                                       else (case (minViewSure kr xr rl rr) of λ { (MinViewCon km m r') → balanceL km m l r'})
  {-# COMPILE AGDA2HS glue #-}


  link2 : Map k a → Map k a → Map k a
  link2 Tip r   = r
  link2 l Tip   = l
  link2 l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry) =
    if (delta * sizeL < sizeR)
    then (balanceL ky y (link2 l ly) ry)
    else (if (delta * sizeR < sizeL)
          then (balanceR kx x lx (link2 rx r))
          else (glue l r))
  {-# COMPILE AGDA2HS link2 #-}

open Linking public
