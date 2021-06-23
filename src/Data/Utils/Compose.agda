module Data.Utils.Compose where

open import Haskell.Prelude

{-------------------
  Data.Functor.Compose
-------------------}

data Compose (f g : Set → Set) (a : Set) : Set where
  ComposeCon : f (g a) → Compose f g a

getCompose : {f g : Set → Set} {a : Set} → Compose f g a → f (g a)
getCompose (ComposeCon x) = x

instance
  iFunctorCompose : {f g : Set → Set} {{_ : Functor f}} {{_ : Functor g}}
                    → Functor (Compose f g)
  iFunctorCompose .fmap f (ComposeCon x) = ComposeCon (fmap (fmap f) x)

  iApplicativeCompose : {f g : Set → Set} {{_ : Applicative f}} {{_ : Applicative g}}
                    → Applicative (Compose f g)
  iApplicativeCompose .pure x = ComposeCon (pure (pure x))
  iApplicativeCompose ._<*>_ (ComposeCon f) (ComposeCon x) = ComposeCon (pure (_<*>_) <*> f <*> x)
