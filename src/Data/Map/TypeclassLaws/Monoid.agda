module Data.Map.TypeclassLaws.Monoid where

open import Haskell.Prelude hiding (map)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances

open import Data.Map.Internal.Construction
open import Data.Map.Internal.Unions
open import Data.Map.Internal.Inserting
open import Data.Map.Internal.Balancing

open import Data.Utils.Reasoning

monoidRightIdentityMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
      → (m : Map k a) → m <> mempty ≡ m
monoidRightIdentityMap Tip = refl
monoidRightIdentityMap (Bin sz kx x l r) = refl


monoidLeftIdentityMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
      → (m : Map k a) → mempty <> m ≡ m
monoidLeftIdentityMap Tip = refl
monoidLeftIdentityMap (Bin sz kx x l r) = refl

monoidConcatenationMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
      → (ms : List (Map k a)) → mconcat ms ≡ foldr (_<>_) mempty ms
monoidConcatenationMap [] = refl
monoidConcatenationMap ms@(x ∷ xs) = begin
    mconcat (x ∷ xs)
  ≡⟨⟩
    x <> mconcat xs
  ≡⟨ cong (λ t → x <> t) (monoidConcatenationMap xs) ⟩
    x <> (foldr (_<>_) mempty xs)
  ≡⟨⟩
    foldr (union) mempty (x ∷ xs)
  ∎
