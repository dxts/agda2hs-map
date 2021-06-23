module Data.Utils.Applicative where

open import Haskell.Prelude

open import Data.Utils.Reasoning

liftA3 : {a b c d : Set} → {f : Set → Set} ⦃ _ : Applicative f ⦄
          → (a → b → c → d) → f a → f b → f c → f d
liftA3 f a b c = (pure f) <*> a <*> b <*> c

postulate
  applicativeHomomorphism : {A B : Set} {p : Set → Set} {{ap : Applicative p}}
      → (f : A → B) (x : A)
      → (pure {p} f <*> pure {p} x) ≡ (pure {p} (f x))

  applicativeFunctorLaw : {A B : Set} {p : Set → Set} {{ap : Applicative p}}
      → (f : A → B) (x : p A)
      → fmap f x ≡ (pure f <*> x)
