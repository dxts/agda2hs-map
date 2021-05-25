module Data.Map.Datatype where

open import Haskell.Prim.Int
{-# FOREIGN AGDA2HS
import Data.Int (Int)
#-}

open import Haskell.Prelude

open import Data.Utils.PartialOrder

open Data.Utils.PartialOrder public

{-------------------
  Map
-------------------}

data Map (k : Set) (a : Set) ⦃ _ : Ord k ⦄ {lower upper : [ k ]∞ } : Set

size : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
       → Map k a { lower } { upper } → Int

data Map k a ⦃ _ ⦄ {lower} {upper} where

  Bin : (sz : Int) {_ : IsNonNegativeInt sz} → (kx : k) → (x : a)
        → (l : Map k a {lower} {[ kx ]}) → (r : Map k a {[ kx ]} {upper})
        → {_ : sz ≡ (size l) + (size r) + 1}
        → Map k a {lower} {upper}

  Tip : ⦃ l≤u : lower ≤ upper ⦄ → Map k a
{-# COMPILE AGDA2HS Map #-}

-- size : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
--        → Map k a { lower } { upper } → Int
size Tip = 0
size (Bin sz _ _ _ _) = sz
{-# COMPILE AGDA2HS size #-}
