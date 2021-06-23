module Data.Map.TypeclassLaws.Functor where

open import Haskell.Prelude hiding (map)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances
open import Data.Map.Internal.Mapping

open import Data.Utils.Reasoning


mapIdentityMap : {k a : Set} {{_ : Ord k}} → (m : Map k a) → map id m ≡ id m
mapIdentityMap Tip = refl
mapIdentityMap (Bin sz kx x l r) =
  begin
    map id (Bin sz kx x l r)
  ≡⟨ cong (λ t →  Bin sz kx x t (map id r)) (mapIdentityMap l) ⟩
    Bin sz kx x l (map id r)
  ≡⟨ cong (λ t →  Bin sz kx x l t) (mapIdentityMap r) ⟩
    Bin sz kx x l r
  ∎

functorIdentityMap : {k a : Set} {{_ : Ord k}} → (m : Map k a) → fmap id m ≡ id m
functorIdentityMap Tip = refl
functorIdentityMap (Bin sz kx x l r) =
  begin
    fmap id (Bin sz kx x l r)
  ≡⟨ cong (λ t →  Bin sz kx x t (map id r)) (functorIdentityMap l) ⟩
    Bin sz kx x l (map id r)
  ≡⟨ cong (λ t →  Bin sz kx x l t) (functorIdentityMap r) ⟩
    Bin sz kx x l r
  ∎

functorCompositionMap : {k a : Set} {{_ : Ord k}} → (f : b → c) (g : a → b) (m : Map k a)
                    → fmap (f ∘ g) m ≡ (fmap f ∘ fmap g) m
functorCompositionMap f g Tip = refl
functorCompositionMap f g m@(Bin sz kx x l r) = begin
    fmap (f ∘ g) (Bin sz kx x l r)
  ≡⟨⟩
    Bin sz kx ((f ∘ g) x) (map (f ∘ g) l) (map (f ∘ g) r)
  ≡⟨ cong (λ t →  Bin sz kx ((f ∘ g) x) t (map (f ∘ g) r))
      (functorCompositionMap f g l) ⟩
    Bin sz kx ((f ∘ g) x) (map f (map g l)) (map (f ∘ g) r)
  ≡⟨ cong (λ t →  Bin sz kx ((f ∘ g) x) (map f (map g l)) t)
      (functorCompositionMap f g r) ⟩
    Bin sz kx (f (g x)) (map f (map g l)) (map f (map g r))
  ≡⟨⟩
    fmap f (fmap g m)
  ∎
