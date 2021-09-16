module Data.Map.BalancingProofs where

open import Haskell.Prelude hiding (map)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances

open import Data.Map.Internal.Balancing

open import Data.Utils.Reasoning




-- balancing definition

singleL :  {k a : Set} -> k -> a -> Map k a -> Map k a -> Map k a
singleL k1 x1 t1 (Tip) = bin k1 x1 t1 Tip
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3

singleR :  {k a : Set} -> k -> a -> Map k a -> Map k a -> Map k a
singleR k1 x1 (Tip) t3  = bin k1 x1 Tip t3
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)


doubleL :  {k a : Set} -> k -> a -> Map k a -> Map k a -> Map k a
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL k1 x1 t1 t2 = bin k1 x1 t1 t2

doubleR :  {k a : Set} -> k -> a -> Map k a -> Map k a -> Map k a
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR k1 x1 t1 t2 = bin k1 x1 t1 t2

rotateL : {k a : Set}
          -> k -> a -> Map k a -> Map k a -> Map k a
rotateL k x l r@Tip = bin k x l r
rotateL k x l r@(Bin _ _ _ ly ry) =
    if (size ly < ratio * size ry)
    then (singleL k x l r)
    else (doubleL k x l r)

rotateR : {k a : Set}
          -> k -> a -> Map k a -> Map k a -> Map k a
rotateR k x l@Tip r = bin k x l r
rotateR k x l@(Bin _ _ _ ly ry) r =
    if (size ry < ratio * size ly)
    then (singleR k x l r)
    else (doubleR k x l r)


balance' : {k a : Set} {{_ : Ord k}}
          -> k -> a -> Map k a -> Map k a -> Map k a
balance' k x l r =
  if (sizeL + sizeR <= 1)
  then (Bin sizeX k x l r)
  else (if (sizeR > delta * sizeL)
        then (rotateL k x l r)
        else (if (sizeL > delta * sizeR)
              then (rotateR k x l r)
              else (Bin sizeX k x l r)))
  where
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1


-- Equality of definitions
equalityOfBalanceDefs : {k a : Set} {{_ : Ord k}}
    -> (k1 : k) (x1 : a) (l r : Map k a)
    -> balance k1 x1 l r ≡ balance' k1 x1 l r
equalityOfBalanceDefs k x Tip Tip = refl
equalityOfBalanceDefs k x Tip r@(Bin sz kr xr Tip Tip) = begin
   Bin (sz + 1) k x Tip (Bin sz kr xr Tip Tip)
  ≡⟨ {!   !} ⟩
   {! Bin (size Tip + size r + 1) k x Tip (Bin sz kr xr Tip Tip)  !}
  ∎
equalityOfBalanceDefs k x Tip r@(Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) = {!   !}
equalityOfBalanceDefs k x Tip r@(Bin _ rk rx rl@(Bin _ rlk rlx _ _) Tip) = {!   !}
equalityOfBalanceDefs k x Tip r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) = {!   !}

equalityOfBalanceDefs k x (Bin sz kl xl ll llr) r = {!   !}
