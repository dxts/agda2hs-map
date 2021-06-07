module Data.Utils.Applicative where

open import Haskell.Prelude

liftA3 : {a b c d : Set} → {f : Set → Set} ⦃ _ : Applicative f ⦄
          → (a → b → c → d) → f a → f b → f c → f d
liftA3 f a b c = (pure f) <*> a <*> b <*> c
