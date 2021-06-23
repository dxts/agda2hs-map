module Data.Utils.Foldable where

open import Haskell.Prelude

fold : {a : Set} {t : Set → Set} {{_ : Foldable t}}
      → ⦃ Monoid a ⦄ → t a → a
fold = foldMap id
