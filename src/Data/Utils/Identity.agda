module Data.Utils.Identity where

open import Haskell.Prelude

{-------------------
  Data.Functor.Identity
-------------------}

data Identity (a : Set) : Set where
  IdentityCon : a → Identity a

runIdentity : Identity a → a
runIdentity (IdentityCon x) = x

instance
  iFunctorIdentity : Functor Identity
  iFunctorIdentity .fmap f (IdentityCon a) = IdentityCon (f a)

  iApplicativeIdentity : Applicative Identity
  iApplicativeIdentity .pure = IdentityCon
  iApplicativeIdentity ._<*>_ (IdentityCon f) (IdentityCon a) = IdentityCon (f a)
