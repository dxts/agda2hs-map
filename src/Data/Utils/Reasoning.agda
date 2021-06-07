module Data.Utils.Reasoning where

open import Haskell.Prelude
open import Agda.Builtin.Equality


{-----
  `inspect` idiom
-----}

-- Used for the inspect idiom.
-- see : https://agda.readthedocs.io/en/v2.6.1.3/language/with-abstraction.html#the-inspect-idiom
data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


{-----
  Equational reasoning methods
-----}

_ : {x : Set} → x ≡ x
_ = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p


{-----
  Equational reasoning re-write functions
-----}


begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

_≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ q = x ≡⟨ refl ⟩ q

infix 1 begin_
infix 3 _∎
infixr 2 _≡⟨_⟩_
infixr 2 _≡⟨⟩_
