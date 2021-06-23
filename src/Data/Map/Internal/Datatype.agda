module Data.Map.Internal.Datatype where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

{-# FOREIGN AGDA2HS
import Data.Nat (Nat)
#-}


{-------------------
  Map
-------------------}


mutual

  data Map (k : Set) (a : Set) : Set where
    Bin : (sz : Nat) → (kx : k) → (x : a)
          → (l : Map k a) → (r : Map k a)
          → Map k a
    Tip : Map k a
  {-# COMPILE AGDA2HS Map #-}

  size : {k a : Set} → Map k a → Nat
  size Tip = 0
  size (Bin sz _ _ _ _) = sz
  {-# COMPILE AGDA2HS size #-}

bin : {k a : Set} → k → a → Map k a → Map k a → Map k a
bin k x l r = Bin (size l + size r + 1) k x l r
{-# COMPILE AGDA2HS bin #-}
