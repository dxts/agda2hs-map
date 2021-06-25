module Data.Map.TypeclassLaws.Eq where

open import Haskell.Prelude

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances

open import Data.Map.Internal.Lists
open import Data.Map.Internal.Folding

open import Data.Utils.Reasoning


postulate
  eqReflexivityList : {a : Set} {{_ : Eq a}} → (xs : List a) → (xs == xs) ≡ true
  eqSymmetryList : {a : Set} {{_ : Eq a}} → (xs ys : List a) → (xs == ys) ≡ (ys == xs)
  eqTransitivityList : {a : Set} {{_ : Eq a}} → (xs ys zs : List a)
      → (xs == ys) ≡ true → (ys == zs) ≡ true → (xs == zs) ≡ true
  eqSubstitutivityList : {a b : Set} {{_ : Eq a}} {{_ : Eq b}}
      → (xs ys : List a) (f : List a → b)
      → (xs == ys) ≡ true → (f xs == f ys) ≡ true
  eqNegationList : {a : Set} {{_ : Eq a}} → (xs ys : List a) → (xs /= ys) ≡ not (xs == ys)

postulate
  eqReflexivityNat : (x : Nat) → (x == x) ≡ true
  eqSymmetryNat : (x y : Nat) → (x == y) ≡ (y == x)
  eqTransitivityNat : (x y z : Nat) → (x == y) ≡ true → (y == z) ≡ true
      → (x == z) ≡ true
  eqSubstitutivityNat : {a : Set} {{_ : Eq a}}
      → (f : Nat → a) (x y : Nat)
      → (x == y) ≡ true → (f x == f y) ≡ true
  eqNegationNat : (x y : Nat) → (x /= y) ≡ not (x == y)




splitAndTruthFst : {A B : Set} {{_ : Eq A}} {{_ : Eq B}}
    → (a1 a2 : A) (b1 b2 : B)
    → (a1 == a2 && b1 == b2) ≡ true
    → (a1 == a2) ≡ true
splitAndTruthFst a1 a2 _ _ prf with (a1 == a2)
... | true = refl

splitAndTruthSnd : {A B : Set} {{_ : Eq A}} {{_ : Eq B}}
  → (a1 a2 : A) (b1 b2 : B)
  → (a1 == a2 && b1 == b2) ≡ true
  → (b1 == b2) ≡ true
splitAndTruthSnd a1 a2 b1 b2 prf with (a1 == a2) | (b1 == b2)
... | true | true = refl





eqReflexivityMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
    → (m : Map k a) → (m == m) ≡ true
eqReflexivityMap t =
  begin
    (size t == size t) && (toAscList t == toAscList t)
  ≡⟨ cong (λ y → y && (toAscList t == toAscList t)) (eqReflexivityNat (size t)) ⟩
    true && (toAscList t == toAscList t)
  ≡⟨ cong (λ y → true && y) (eqReflexivityList (toAscList t)) ⟩
    true && true
  ≡⟨⟩
    true
  ∎

eqSymmetryMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
    → (m1 m2 : Map k a) → (m1 == m2) ≡ (m2 == m1)
eqSymmetryMap m1 m2 =
  begin
    (size m1 == size m2) && (toAscList m1 == toAscList m2)
  ≡⟨ cong (λ y → y && (toAscList m1 == toAscList m2)) (eqSymmetryNat (size m1) (size m2)) ⟩
    (size m2 == size m1) && (toAscList m1 == toAscList m2)
  ≡⟨ cong (λ y → (size m2 == size m1) && y) (eqSymmetryList (toAscList m1) (toAscList m2)) ⟩
    ((size m2 == size m1) && (toAscList m2 == toAscList m1))
  ∎

eqTransitivityMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
    → (m1 m2 m3 : Map k a) → (m1 == m2) ≡ true → (m2 == m3) ≡ true
    → (m1 == m3) ≡ true
eqTransitivityMap m1 m2 m3 prf1 prf2 =
  begin
    (size m1 == size m3) && (toAscList m1 == toAscList m3)

  ≡⟨ (
    let prf1' = (splitAndTruthFst (size m1) (size m2) (toAscList m1) (toAscList m2) prf1)
        prf2' = (splitAndTruthFst (size m2) (size m3) (toAscList m2) (toAscList m3) prf2)
    in cong (λ y → y && (toAscList m1 == toAscList m3)) (eqTransitivityNat (size m1) (size m2) (size m3) prf1' prf2')
    ) ⟩
    true && (toAscList m1 == toAscList m3)

  ≡⟨ (
    let prf1' = (splitAndTruthSnd (size m1) (size m2) (toAscList m1) (toAscList m2) prf1)
        prf2' = (splitAndTruthSnd (size m2) (size m3) (toAscList m2) (toAscList m3) prf2)
    in cong (λ y → true && y) (eqTransitivityList (toAscList m1) (toAscList m2) (toAscList m3) prf1' prf2')
    ) ⟩
    true
  ∎


{-
  Doesn't hold for Map equality
  Map equality is weakly defined as two maps containing the same elements
  But two equal maps could have different representations in the Map constructor
  ```
  f : {k a : Set} → Map k a → Nat
  f Tip = 0
  f (Bin _ _ _ l r) = 1 + (f l)
  ```

  map1 = Bin 2 "b" "val" (singleton "a" "val") (Tip)
  map2 = Bin 2 "a" "val" (Tip) (singleton "b" "val")

  map1 == map2 ≡ true

  (f map1) == (f map2) =>  2 == 1 ̸≡ true
-}
eqSubstitutivityMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
    → {b : Set} {{_ : Eq b}} (f : Map k a → b)
    → (m1 m2 : Map k a) → (m1 == m2) ≡ true
    → (f m1 == f m2) ≡ true
eqSubstitutivityMap f m1 m2 prf = {!   !}



eqNegationMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
    → (m1 m2 : Map k a) → (m1 /= m2) ≡ not (m1 == m2)
eqNegationMap m1 m2 = refl
