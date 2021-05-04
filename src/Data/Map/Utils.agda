module Data.Map.Utils where

open import Haskell.Prelude

-- Can be used to apply conditions on inputs in the type signature
-- and cause absurd patterns when they are not met.
data Holds : Bool → Set where
  doesHold : Holds true

-- Used for the inspect idiom.
-- see : https://agda.readthedocs.io/en/v2.6.1.3/language/with-abstraction.html#the-inspect-idiom
data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl
