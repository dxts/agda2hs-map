module Data.Map.Internal.Instances where

open import Haskell.Prelude hiding (map)
{-# FOREIGN AGDA2HS
import Prelude hiding (map)
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

open import Data.Map.Internal.Mapping
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Mapping
#-}

open import Data.Map.Internal.Unions
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Unions
#-}

instance
  iSemigroupMap : {k a : Set} → ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ ⦃ _ : Eq (Map k a) ⦄
                  → Semigroup (Map k a)
  iSemigroupMap ._<>_ = union
  {-# COMPILE AGDA2HS iSemigroupMap #-}


  iMonoidMap : {k a : Set} → ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ ⦃ _ : Eq (Map k a) ⦄
               → Monoid (Map k a)
  iMonoidMap .mempty = empty
  {-# COMPILE AGDA2HS iMonoidMap #-}


  iEqMap : {k a : Set} ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ → Eq (Map k a)
  iEqMap ._==_ t1 t2 = (size t1 == size t2) && (toAscList t1 == toAscList t2)
  {-# COMPILE AGDA2HS iEqMap #-}


  -- iOrdMap : {k a : Set} ⦃ _ : Ord k ⦄ ⦃ _ : Ord a ⦄ → Ord (Map k a)
  -- iOrdMap = ordFromCompare (λ t1 t2 → compare (toAscList t1) (toAscList t2))
  -- {-# COMPILE AGDA2HS iOrdMap #-}

  iFunctorMap : {k : Set} ⦃ _ : Ord k ⦄ → Functor (Map k)
  iFunctorMap .fmap f m = map f m
  {-# COMPILE AGDA2HS iFunctorMap #-}

  iFoldableMap : {k : Set} ⦃ _ : Ord k ⦄ → Foldable (Map k)
  iFoldableMap .foldMap f Tip = mempty
  iFoldableMap .foldMap f (Bin 1 _ v _ _) = f v
  iFoldableMap .foldMap f (Bin _ _ v l r) = mappend (foldMap f l) (mappend (f v) (foldMap f r))
  {-# COMPILE AGDA2HS iFoldableMap #-}

  iTraversableMap : {k : Set} ⦃ _ : Ord k ⦄ → Traversable (Map k)
  iTraversableMap .traverse f m = traverseWithKey (λ _ → f) m
  {-# COMPILE AGDA2HS iTraversableMap #-}
