module Data.Utils.PartialOrder where

open import Agda.Builtin.TrustMe
open import Agda.Builtin.Equality
open import Data.Utils.Reasoning

open import Haskell.Prelude

variable
  A : Set
  x y z : A


data [_]∞ (A : Set) : Set where
  -∞  :     [ A ]∞
  [_] : A → [ A ]∞
  +∞  :     [ A ]∞

variable
  lower upper : [ A ]∞

module Ord-[]∞ {A : Set} ⦃ A-≤ : Ord A ⦄ where

  _≤_ : A → A → Set
  x ≤ y = (x <= y) ≡ true

  ≤-refl : x ≤ x
  ≤-refl {x} = primTrustMe

  ≤-trans : x ≤ y → y ≤ z → x ≤ z
  ≤-trans prf1 prf2 = primTrustMe

  ≤-antisym : x ≤ y → y ≤ x → x ≡ y
  ≤-antisym prf1 prf2 = primTrustMe

  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ :          -∞   ≤∞   y
    []-≤ :  x ≤ y → [ x ] ≤∞ [ y ]
    +∞-≤ :           x   ≤∞  +∞

  []∞-refl : x ≤∞ x
  []∞-refl { -∞}   = -∞-≤
  []∞-refl {[ x ]} = []-≤ ≤-refl
  []∞-refl { +∞}   = +∞-≤

  []∞-trans : x ≤∞ y → y ≤∞ z → x ≤∞ z
  []∞-trans -∞-≤       _          = -∞-≤
  []∞-trans ([]-≤ x≤y) ([]-≤ y≤z) = []-≤ (≤-trans x≤y y≤z)
  []∞-trans _          +∞-≤       = +∞-≤

  []∞-antisym : x ≤∞ y → y ≤∞ x → x ≡ y
  []∞-antisym -∞-≤       -∞-≤       = refl
  []∞-antisym ([]-≤ x≤y) ([]-≤ y≤x) = cong [_] (≤-antisym x≤y y≤x)
  []∞-antisym +∞-≤       +∞-≤       = refl

  instance
    Eq-[]∞ : Eq [ A ]∞
    Eq-[]∞ ._==_ -∞ -∞ = true
    Eq-[]∞ ._==_ [ a ] [ b ] = a == b
    Eq-[]∞ ._==_ +∞ +∞ = true
    Eq-[]∞ ._==_ _ _ = false


    Ord-[]∞ : Ord [ A ]∞
    Ord-[]∞ = ordFromLessEq ple
      where
        ple : (a : [ A ]∞) → (b : [ A ]∞) → Bool
        ple _ +∞  = true
        ple [ a ] [ b ] = a <= b
        ple -∞ _  = true
        ple _ _ = false

open Ord-[]∞ public
