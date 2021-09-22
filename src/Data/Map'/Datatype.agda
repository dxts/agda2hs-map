module Data.Map'.Datatype where


open import Haskell.Prelude

open import Data.Utils.PartialOrder public


{-------------------
  Map
-------------------}


data Map (k : Set) (a : Set) ⦃ kOrd : Ord k ⦄ {lower upper : [ k ]∞} : Set where
  Bin : (sz : Nat) → (kx : k) → (x : a)
        → (l : Map k a {lower} {[ kx ]}) → (r : Map k a {[ kx ]} {upper})
        → Map k a {lower} {upper}

  Tip : ⦃ l≤u : lower ≤ upper ⦄ → Map k a {lower} {upper}
{-# COMPILE AGDA2HS Map #-}


size : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
       → Map k a { lower } { upper } → Nat
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



subUpperBound : {k a : Set} {{_ : Ord k}} {l u1 u2 : [ k ]∞}
  → Map k a {l} {u1} → { u1 ≡ u2 } → Map k a {l} {u2}
subUpperBound  map {refl} = map
{-# INLINE subUpperBound #-}

subLowerBound : {k a : Set} {{_ : Ord k}} {l1 l2 u : [ k ]∞}
  → Map k a {l1} {u} → { l1 ≡ l2 } → Map k a {l2} {u}
subLowerBound  map {refl} = map
{-# INLINE subLowerBound #-}


postulate
  LBisLower : {k a : Set} {{_ : Ord k}} {l u : [ k ]∞}
    → (m : Map k a {l} {u}) → {ne : isEmpty m ≡ false}
    → l ≤ [ getKey m {ne}]

  UBisHigher : {k a : Set} {{_ : Ord k}} {l u : [ k ]∞}
    → (m : Map k a {l} {u}) → {ne : isEmpty m ≡ false}
    → [ getKey m {ne}] ≤ u
