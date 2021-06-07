module Data.Map.Internal.Instances where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

open import Data.Map.Internal.Lists
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Lists
#-}

open import Data.Map.Internal.Unions
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Unions
#-}

instance
  iSemigroupMap : {k a : Set} → ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ ⦃ _ : Eq (Map k a) ⦄
                  → Semigroup (Map k a)
  Semigroup._<>_ (iSemigroupMap) = union
  {-# COMPILE AGDA2HS iSemigroupMap #-}


  iMonoidMap : {k a : Set} → ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ ⦃ _ : Eq (Map k a) ⦄
               → Monoid (Map k a)
  Monoid.mempty (iMonoidMap) = empty
  {-# COMPILE AGDA2HS iMonoidMap #-}


  iEqMap : {k a : Set} ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ → Eq (Map k a)
  Eq._==_ (iEqMap) t1 t2 = (size t1 == size t2) && (toAscList t1 == toAscList t2)
  {-# COMPILE AGDA2HS iEqMap #-}


  -- iOrdMap : {k a : Set} ⦃ _ : Ord k ⦄ ⦃ _ : Ord a ⦄ → Ord (Map k a)
  -- iOrdMap = ordFromCompare (λ t1 t2 → compare (toAscList t1) (toAscList t2))
  -- {-# COMPILE AGDA2HS iOrdMap #-}
