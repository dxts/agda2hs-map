module Data.Map.FunctorLaws where

open import Haskell.Prelude hiding (map)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances
open import Data.Map.Internal.Mapping

open import Data.Utils.Reasoning



-- binEquality : {k a : Set} {{_ : Ord k}} → (sz : Nat) (kx : k) (x : a) (l r : Map k a) (szVal : sz ≡ (size l + size r + 1)) → bin kx x l r ≡ Bin sz kx x l r {szVal}
-- binEquality sz kx x l r szVal = begin
--     bin kx x l r
--   ≡⟨⟩
--     Bin (size l + size r + 1) kx x l r {refl}
--   ≡⟨ cong' sz kx x l r szVal ⟩
--     Bin sz kx x l r {szVal}
--   ∎

--   where
--     cong' : {k a : Set} → (sz : Nat) (kx : k) (x : a) (l r : Map k a) (szVal : sz ≡ (size l + size r + 1)) → (Bin (size l + size r + 1) kx x l r {refl}) ≡ (Bin sz kx x l r {szVal})
--     cong' sz kx x l r szVal = {!   !}


-- mapIdentity : {k a : Set} {{_ : Ord k}} → (m : Map k a) → map id m ≡ id m
-- mapIdentity Tip = refl
-- mapIdentity (Bin sz kx x l r {szVal}) =
--   begin
--     map id (Bin sz kx x l r {szVal})
--   ≡⟨ {!   !} ⟩
--     bin kx x l r
--   ∎
-- functorIdentity : {k a : Set} {{_ : Ord k}} → (m : Map k a) → fmap id m ≡ id m
-- functorIdentity Tip = refl
-- functorIdentity (Bin sz kx x l r {szVal}) =
--   begin
--     fmap id (Bin sz kx x l r {szVal})
--   ≡⟨ {! cong (λ x → cong (λ y → ) (functorIdentity r)) (functorIdentity l)  !} ⟩
--     id (Bin sz kx (id x) l r {szVal})
--   ≡⟨⟩
--     id (Bin sz kx x l r {szVal})
--   ∎
