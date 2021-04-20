module Data.Map.Internal where

open import Haskell.Prelude


data Map : (k a : Set) → Set where
  Bin : {k a : Set} → (size : Int) → k → a → Map k a → Map k a → Map k a
  Tip : {k a : Set} → Map k a

{-------------------
  Construction
-------------------}

empty : {k a : Set} → Map k a
empty = Tip

singleton : {k a : Set} → k → a → Map k a
singleton k x = Bin 1 k x Tip Tip

{-------------------
  Insertion
-------------------}

lazy : {a : Set} → a → a
lazy a = a

insert : {k a : Set} → ⦃ Ord k ⦄ → k → a → Map k a → Map k a
insert kx0 = go kx0 kx0
  where
    go : {k a : Set} → ⦃ Ord k ⦄ → k → k → a → Map k a → Map k a
    go orig _  x Tip = singleton (lazy orig) x
    go orig kx x t@(Bin sz ky y l r) = {!   !}
