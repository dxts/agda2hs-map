module Data.Map'.Internal where
{-# FOREIGN AGDA2HS
module Data.Map.Internal
  ( module Data.Map'.Datatype
  , module Data.Map'.Balancing
  , module Data.Map'.Construction
  , module Data.Map'.Insertion
  , module Data.Map'.Query
  ) where

import Data.Map'.Datatype

import Data.Map'.Balancing
import Data.Map'.Construction
import Data.Map'.Insertion
import Data.Map'.Query
#-}

open import Data.Map'.Datatype public

open import Data.Map'.Balancing public
open import Data.Map'.Construction public
open import Data.Map'.Insertion public
open import Data.Map'.Query public
