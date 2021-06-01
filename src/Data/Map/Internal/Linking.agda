{-# OPTIONS --warning noMissingDefinitions #-}

module Data.Map.Internal.Linking where

open import Haskell.Prelude hiding (null)
{-# FOREIGN AGDA2HS
import Prelude hiding (null)
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.Internal.Query
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Query
#-}

module Linking {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  link : ∀ {lower upper : [ k ]∞ } → (kx : k) → a → Map k a {lower} {[ kx ]} → Map k a {[ kx ]} {upper} → Map k a {lower} {upper}

  insertMax : ∀ {lower upper : [ k ]∞ } → k → a → Map k a {lower} {upper} → Map k a {lower} {upper}

  insertMin : ∀ {lower upper : [ k ]∞ } → k → a → Map k a {lower} {upper} → Map k a {lower} {upper}

  link2 : ∀ {lower upper : [ k ]∞ } → Map k a {lower} {upper} → Map k a {lower} {upper} → Map k a {lower} {upper}

  glue : ∀ {lower upper : [ k ]∞ } → Map k a {lower} {upper} → Map k a {lower} {upper} → Map k a {lower} {upper}

  data MinView (k a : Set) ⦃ _ : Ord k ⦄ : Set where
    MinViewCon : ∀ {lower upper : [ k ]∞ } → k → a → (Map k a {lower} {upper}) → MinView k a

  data MaxView (k a : Set) ⦃ _ : Ord k ⦄ : Set where
    MaxViewCon : ∀ {lower upper : [ k ]∞ } → k → a → (Map k a {lower} {upper}) → MaxView k a

  minViewSure : ∀ {lower upper : [ k ]∞ } → k → a → Map k a {lower} {upper} → Map k a {lower} {upper} → MinView k a

  maxViewSure : ∀ {lower upper : [ k ]∞ } → k → a → Map k a {lower} {upper} → Map k a {lower} {upper} → MaxView k a

  deleteFindMin : ∀ {lower upper : [ k ]∞ } → (map : Map k a {lower} {upper}) → {IsTrue (not (null map))} → ((k × a) × Map k a {lower} {upper})

  deleteFindMax : ∀ {lower upper : [ k ]∞ } → (map : Map k a {lower} {upper}) → {IsTrue (not (null map))} → ((k × a) × Map k a {lower} {upper})


open Linking public
