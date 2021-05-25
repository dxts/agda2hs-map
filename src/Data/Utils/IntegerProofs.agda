module Data.Utils.IntegerProofs where

open import Haskell.Prelude

-- additionPos : (m n : Int) {mPos : IsNonNegativeInt m} {nPos : IsNonNegativeInt n}
--                 → IsNonNegativeInt (m + n + 1)
-- additionPos (int64 x) (int64 x₁) {mPos} {nPos} with x + x₁ + 1
-- ... | sum = {!  !}

postulate
  subtractionPos : (m n : Int) {mPos : IsNonNegativeInt m} {nPos : IsNonNegativeInt n}
                    → (eq : compare m n ≡ GT) → IsNonNegativeInt (m - n - 1)

  additionPos : (m n : Int) {mPos : IsNonNegativeInt m} {nPos : IsNonNegativeInt n}
                → IsNonNegativeInt (m + n + 1)
