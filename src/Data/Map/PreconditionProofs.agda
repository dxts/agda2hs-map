module Data.Map.PreconditionProofs where

open import Haskell.Prelude

open import Data.Map.Datatype

open import Data.Utils.Reasoning
open import Data.Utils.IntegerProofs


{--------------------
  Functions to enforce preconditions
--------------------}

_∈_ : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
      → k → Map k a { lower } { upper } → Bool
_ ∈ Tip = false
k ∈ (Bin _ kx _ l r) with (compare k kx)
... | LT = k ∈ l
... | GT = k ∈ r
... | EQ = true

_[_]≤_ : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
         → (n : Int) → (_ : IsNonNegativeInt n) → Map k a { lower } { upper } → Bool
_[_]≤_ n nPos map with (compare n (size map))
... | LT = true
... | GT = false
... | EQ = false



{--------------------
  Functions to transform proofs, eg : shrinking pre-condition proofs
--------------------}

sizeIsPos : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
            → (map : Map k a {lower} {upper}) → IsNonNegativeInt (size map)
sizeIsPos Tip = tt
sizeIsPos (Bin sz {szPos} _ _ _ _) = szPos

∈L : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
          → (sz : Int) {szPrf : IsNonNegativeInt sz} (key kx : k) (x : a) (l : Map k a {lower} {[ kx ]}) (r : Map k a {[ kx ]} {upper})
          → (eq : compare key kx ≡ LT)
          → (prf : IsTrue (key ∈ (Bin sz {szPrf} kx x l r)))
          → (IsTrue (key ∈ l))
∈L sz key kx x l r eq prf with compare key kx
... | LT = prf


∈R : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
          → (sz : Int) {szPrf : IsNonNegativeInt sz} (key kx : k) (x : a) (l : Map k a {lower} {[ kx ]}) (r : Map k a {[ kx ]} {upper})
          → (eq : compare key kx ≡ GT)
          → (prf : IsTrue (key ∈ (Bin sz {szPrf} kx x l r)))
          → (IsTrue (key ∈ r))
∈R sz key kx x l r eq prf with compare key kx
... | GT = prf



∈[L] : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
        → (n : Int) {nPrf : IsNonNegativeInt n} (l : Map k a {lower} {upper})
            → (eq : compare n (size l) ≡ LT)
            → IsTrue (n [ nPrf ]≤ l)
∈[L] n l eq with (compare n (size l))
... | LT = IsTrue.itsTrue

postulate ∈[R] : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
                  → (n : Int) {nPos : IsNonNegativeInt n} (l r : Map k a {lower} {upper})
                  → (eq : compare n (size l) ≡ GT) {iPos : IsNonNegativeInt (n - (size l) - 1)}
                  →  IsTrue ((n - (size l) - 1) [ iPos ]≤ r)
-- ∈[R] : {k a : Set} → (n : Int) {nPos : IsNonNegativeInt n} (l r : Map k a) {lPos : IsNonNegativeInt (size l)}
--             → (eq : compare n (size l) ≡ GT)
--             → {bogus : (n - (size l) - 1) ≡ (size r - 1)} {iPos : IsNonNegativeInt (n - (size l) - 1)}
--             → IsTrue ((n - (size l) - 1) [ iPos ]≤ r)
-- ∈[R] n l r eq {bog} with (compare n (size l))
-- ... | GT = {!  IsTrue.itsTrue !}
