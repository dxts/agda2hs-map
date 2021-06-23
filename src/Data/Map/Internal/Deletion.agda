module Data.Map.Internal.Deletion where

{-# FOREIGN AGDA2HS {-# LANGUAGE FlexibleContexts #-} #-}

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

open import Data.Map.Internal.Balancing
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Balancing
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

open import Data.Map.Internal.Construction
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Construction
#-}

module Deletion {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  delete : ⦃ Eq (Map k a) ⦄ → k → Map k a → Map k a
  delete _ Tip                = Tip
  delete k t@(Bin _ kx x l r) = case (compare k kx) of
      λ {
        LT → let l' = delete k l in if (l' == l) then t else balanceR kx x l' r
      ; GT → let r' = delete k r in if (r' == r) then t else balanceL kx x l r'
      ; EQ → glue l r
      }
  {-# COMPILE AGDA2HS delete #-}


  adjustWithKey : (k → a → a) → k → Map k a → Map k a
  adjustWithKey _ _ Tip               = Tip
  adjustWithKey f k (Bin sz  kx x l r) = case (compare k kx) of
      λ {
        LT → bin kx x (adjustWithKey f k l) r
      ; GT → bin kx x l (adjustWithKey f k r)
      ; EQ → bin kx (f kx x) l r
      }
  {-# COMPILE AGDA2HS adjustWithKey #-}

  adjust : (a → a) → k → Map k a → Map k a
  adjust f = adjustWithKey (λ _ x → f x)
  {-# COMPILE AGDA2HS adjust #-}


  updateWithKey : (k → a → Maybe a) → k → Map k a → Map k a
  updateWithKey _ _ Tip               = Tip
  updateWithKey f k (Bin sz kx x l r) = case (compare k kx) of
      λ {
        LT → balanceR kx x (updateWithKey f k l) r
      ; GT → balanceL kx x l (updateWithKey f k r)
      ; EQ → case (f kx x) of
          λ {
            (Just x') → Bin sz kx x' l r
          ; Nothing → glue l r
          }
      }
  {-# COMPILE AGDA2HS updateWithKey #-}

  update : (a → Maybe a) → k → Map k a → Map k a
  update f = updateWithKey (λ _ x → f x)
  {-# COMPILE AGDA2HS update #-}

  updateLookupWithKey : (k → a → Maybe a) → k → Map k a → (Maybe a × Map k a)
  updateLookupWithKey _ _ Tip               = (Nothing , Tip)
  updateLookupWithKey f k (Bin sz kx x l r) = case (compare k kx) of
      λ {
        LT → let res = updateLookupWithKey f k l
                 t' = balanceR kx x (snd res) r
                 in (fst res , t')
      ; GT → let res = updateLookupWithKey f k r
                 t' = balanceL kx x l (snd res)
                 in (fst res , t')
      ; EQ → case (f kx x) of
          λ {
            (Just x') → (Just x' , Bin sz kx x' l r)
          ; Nothing → (Just x , glue l r)
          }
      }
  {-# COMPILE AGDA2HS updateLookupWithKey #-}

  alter : (Maybe a → Maybe a) → k → Map k a → Map k a
  alter f k Tip = case (f Nothing) of
      λ {
        Nothing → Tip
      ; (Just x) → singleton k x
      }
  alter f k (Bin sz  kx x l r) = case (compare k kx) of
      λ {
        LT → balance kx x (alter f k l) r
      ; GT → balance kx x l (alter f k r)
      ; EQ → case (f (Just x)) of
          λ {
            (Just x') → Bin sz  kx x' l r
          ; Nothing → glue l r
          }
      }
  {-# COMPILE AGDA2HS alter #-}

  -- [TODO] Look into BitQueue
  {-------------------
    alterF
  -------------------}

  -- data AreWeStrict : Set where
  --   Lazy : AreWeStrict
  --   Strict : AreWeStrict

  -- data TraceResult (a : Set) : Set where
  --   TraceResultCon : Maybe a → BitQueue → TraceResult a

  -- atKeyImpl : {k a : Set} {f : Set} → ⦃ Ord k ⦄ → ⦃ Functor f ⦄ → AreWeStrict → k → (Maybe a → f (Maybe a)) → Map k a → f (Map k a)
  -- atKeyImpl strict k f m = case (lookupTrace k m) of
  --     λ {
  --       (TraceResultCon mv q) → (f <$> mv) (λ fres → case fres of
  --           λ {
  --             Nothing → case mv of
  --                 λ {
  --                   Nothing → m
  --                 ; (Just old) → deleteAlong old q m
  --                 }
  --           ; (Just new) → case strict of
  --               λ {
  --                 Strict → seq new (case mv of
  --                     λ {
  --                       Nothing → insertAlong q k new m
  --                     ; (Just _) → replaceAlong q new m
  --                     })
  --               ; Lazy → case mv of
  --                     λ {
  --                       Nothing → insertAlong q k new m
  --                     ; (Just _) → replaceAlong q new m
  --                     }
  --               }
  --           })
  --     }

  -- alterF : {k a : Set} {f : Set} → ⦃ Ord k ⦄ → ⦃ Functor f ⦄ → (Maybe a → f (Maybe a)) → k → Map k a → f (Map k a)
  -- alterF f k m = atKeyImpl Lazy k f m



open Deletion public
