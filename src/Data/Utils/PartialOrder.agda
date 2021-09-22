module Data.Utils.PartialOrder where

open import Agda.Builtin.TrustMe
open import Agda.Builtin.Equality
open import Data.Utils.Reasoning

open import Haskell.Prelude

private
  variable
    A : Set
    x y z : A


data [_]∞ (A : Set) : Set where
  -∞  :     [ A ]∞
  [_] : A → [ A ]∞
  +∞  :     [ A ]∞


module POrd {A : Set} ⦃ iOrdA : Ord A ⦄ where

  {- NOTE : These properties should be required while
    defining an instance of Ord. -}
  postulate
    Ord-equiv : {A : Set} {x y : A} {{_ : Ord A}} → (x == y) ≡ true → x ≡ y
    Ord-refl : {A : Set} {x : A} {{_ : Ord A}} → (x <= x) ≡ true
    Ord-trans : {A : Set} {x y z : A} {{_ : Ord A}} → (x <= y) ≡ true → (y <= z) ≡ true → (x <= z) ≡ true
    Ord-antisym : {A : Set} {x y : A} {{_ : Ord A}} → (x <= y) ≡ true → (y <= x) ≡ true → (x == y) ≡ true
  {---------------------------------------------------------------------------}

  {- Trying to use the Haskell.Prim.Ord type to construct this ordering type -}
  _≤_ : A → A → Set
  x ≤ y = (x <= y) ≡ true

  ≤-refl : x ≤ x
  ≤-refl = Ord-refl {A}

  ≤-trans : x ≤ y → y ≤ z → x ≤ z
  ≤-trans eq1 eq2 = Ord-trans {A} eq1 eq2

  ≤-antisym : x ≤ y → y ≤ x → x ≡ y
  ≤-antisym eq1 eq2 = Ord-equiv (Ord-antisym {A} eq1 eq2)

  instance
    iEq[]∞ : Eq [ A ]∞
    iEq[]∞ ._==_  -∞    -∞    = true
    iEq[]∞ ._==_ [ a ] [ b ]  = a == b
    iEq[]∞ ._==_  +∞    +∞    = true
    iEq[]∞ ._==_   _     _    = false


    iOrd[]∞ : Ord [ A ]∞
    iOrd[]∞ = ordFromLessEq ple
      where
        ple : (a : [ A ]∞) → (b : [ A ]∞) → Bool
        ple  -∞     _   = true
        ple [ a ]  -∞   = false
        ple [ a ] [ b ] = a <= b
        ple [ a ]  +∞   = true
        ple  +∞    -∞   = false
        ple  +∞   [ _ ] = false
        ple  +∞    +∞   = true

open POrd public


postulate
  compareLT-≤ : {A : Set} {{_ : Ord A}} → (x y : A) → compare x y ≡ LT → x ≤ y
  compareGT-≤ : {A : Set} {{_ : Ord A}} → (x y : A) → compare x y ≡ GT → y ≤ x
  compareEQ-≡ : {A : Set} {{_ : Ord A}} → (x y : A) → compare x y ≡ EQ → x ≡ y
  EQ-≤ : {A : Set} {{_ : Ord A}} → (x y : A) → x ≡ y → x ≤ y

postulate
  min-≤1 : {A : Set} {{_ : Ord A}}
    → (x y : A) → (min x y) ≤ x

  min-≤2 : {A : Set} {{_ : Ord A}}
    → (x y : A) → (min x y) ≤ y

  max-≤1 : {A : Set} {{_ : Ord A}}
    → (x y : A) → x ≤ (max x y)

  max-≤2 : {A : Set} {{_ : Ord A}}
    → (x y : A) → y ≤ (max x y)

  ≤-min : {A : Set} {{_ : Ord A}} → (x y : A)
    → x ≤ y → (min x y) ≡ x

  ≤-max : {A : Set} {{_ : Ord A}} → (x y : A)
    → y ≤ x → (max x y) ≡ x
