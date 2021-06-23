module Data.Map.TypeclassLaws.Foldable where

open import Haskell.Prelude hiding (map; foldl; foldr)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances

open import Data.Map.Internal.Folding
open import Data.Map.Internal.Mapping

open import Data.Utils.Foldable

open import Data.Utils.Reasoning


foldableFunctorMap : {k a b : Set} {{_ : Ord k}} {{_ : Monoid b}}
    → (f : a → b) (m : Map k a) → foldMap f m ≡ (fold ∘ fmap f) m
foldableFunctorMap f Tip = refl
foldableFunctorMap f m@(Bin sz kx x l r) = begin
    foldMap f m
  ≡⟨⟩
    mappend (foldMap f l) (mappend (f x) (foldMap f r))
  ≡⟨ cong (λ t → mappend (foldMap f l) (mappend (f x) t)) (foldableFunctorMap f r) ⟩
    mappend (foldMap f l) (mappend (f x) (fold (fmap f r)))
  ≡⟨ cong (λ t → mappend t (mappend (f x) (fold (fmap f r)))) (foldableFunctorMap f l) ⟩
    mappend (foldMap id (map f l)) (mappend (id (f x)) (foldMap id (map f r)))
  ≡⟨⟩
    foldMap id (Bin sz kx (f x) (map f l) (map f r))
  ≡⟨⟩
    foldMap id (fmap f m)
  ≡⟨⟩
    fold (fmap f m)
  ∎
