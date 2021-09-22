module Data.Map.Datatype where


open import Haskell.Prelude

open import Data.Utils.PartialOrder public


{-------------------
  Map
-------------------}


data Map (k : Set) (a : Set) ⦃ kOrd : Ord k ⦄ {lower upper : [ k ]∞} : Set

size : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
       → Map k a { lower } { upper } → Nat


data Map k a ⦃ kOrd ⦄ {lower} {upper} where

  Bin : (sz : Nat) → (kx : k) → (x : a)
        → (l : Map k a {lower} {[ kx ]}) → (r : Map k a {[ kx ]} {upper})
        → Map k a {lower} {upper}

  Tip : ⦃ l≤u : lower ≤ upper ⦄ → Map k a {lower} {upper}
{-# COMPILE AGDA2HS Map #-}


size Tip = 0
size (Bin sz _ _ _ _) = sz
{-# COMPILE AGDA2HS size #-}


isEmpty : {k a : Set} {{_ : Ord k}} → ∀ {l u : [ k ]∞}
  → Map k a {l} {u} → Bool
isEmpty (Bin sz kx x l r) = false
isEmpty Tip = true


getKey : {k a : Set} {{_ : Ord k}} → ∀ {l u : [ k ]∞}
  → (m : Map k a {l} {u}) → {isEmpty m ≡ false} → k
getKey (Bin sz kx x l r) = kx
