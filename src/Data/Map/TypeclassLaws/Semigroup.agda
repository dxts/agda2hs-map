module Data.Map.TypeclassLaws.Semigroup where

open import Haskell.Prelude hiding (map)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances

open import Data.Map.Internal.Unions
open import Data.Map.Internal.Inserting
open import Data.Map.Internal.Balancing

open import Data.Utils.Reasoning


semigroupAssociativityMap : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
          → (m1 m2 m3 : Map k a) → (m1 <> m2) <> m3 ≡ m1 <> (m2 <> m3)
semigroupAssociativityMap Tip Tip Tip = refl
semigroupAssociativityMap Tip Tip m3@(Bin sz kx x l3 l4) = refl
semigroupAssociativityMap Tip m2@(Bin sz kx x l2 r2) m3 = refl

semigroupAssociativityMap (Bin sz kx x l1 r1) Tip m3 = refl
semigroupAssociativityMap m1@(Bin sz1 kx1 x1 l1 r1) m2@(Bin sz2 kx2 x2 Tip Tip) Tip
  with (insertR kx2 x2 m1)
... | Tip = refl
... | m4@(Bin _ _ _ _ _) = refl

semigroupAssociativityMap m1@(Bin sz1 kx1 x1 l1 r1) m2@(Bin sz2 kx2 x2 Tip Tip) m3@(Bin sz3 kx3 x3 Tip Tip) =
  begin
    (insertR kx2 x2 m1) <> m3
  ≡⟨⟩
    {!   !}
  ≡⟨ {!   !} ⟩
    m1 <> (insertR kx3 x3 m2)
  ∎

semigroupAssociativityMap m1@(Bin sz1 kx1 x1 l1 r1) m2@(Bin sz2 kx2 x2 Tip Tip) m3@(Bin sz3 kx3 x3 l3 r3) = {!   !}

semigroupAssociativityMap m1@(Bin sz1 kx1 x1 l1 r1) m2@(Bin sz2 kx2 x2 l2 r2) m3 = {!  !}
