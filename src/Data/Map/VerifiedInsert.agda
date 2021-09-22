module Map.VerifiedInsert where

open import Haskell.Prelude
    hiding (lookup; map; filter; foldr; foldl; null; splitAt; take; drop)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup, map, filter, foldr, foldl, null, splitAt, take, drop)
#-}

open import Data.Map.Datatype

open import Data.Map.Internal.Construction
open import Data.Map.Internal.Balancing

open import Data.Utils.Reasoning


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


subUpperBound : {k a : Set} {{_ : Ord k}} {l u1 u2 : [ k ]∞}
  → Map k a {l} {u1} → { u1 ≡ u2 } → Map k a {l} {u2}
subUpperBound  map {refl} = map
{-# INLINE subUpperBound #-}

subLowerBound : {k a : Set} {{_ : Ord k}} {l1 l2 u : [ k ]∞}
  → Map k a {l1} {u} → { l1 ≡ l2 } → Map k a {l2} {u}
subLowerBound  map {refl} = map
{-# INLINE subLowerBound #-}


postulate
  LBisLower : {k a : Set} {{_ : Ord k}} {l u : [ k ]∞}
    → (m : Map k a {l} {u}) → {ne : isEmpty m ≡ false}
    → l ≤ [ getKey m {ne}]

  UBisHigher : {k a : Set} {{_ : Ord k}} {l u : [ k ]∞}
    → (m : Map k a {l} {u}) → {ne : isEmpty m ≡ false}
    → [ getKey m {ne}] ≤ u



insert : {k a : Set} {{_ : Ord k}} {{_ : Eq a}}
  → {lower upper : [ k ]∞}
  → (ky : k) → (y : a) → (m : Map k a {lower} {upper})
  → Map k a {min lower [ ky ]} {max upper [ ky ]}

insert {lower = lower} {upper = upper} ky y Tip =
  singleton ky y {{min-≤2 lower [ ky ]}} {{max-≤2 upper [ ky ]}}

insert {k} {a} {lower} {upper} ky y m@(Bin sz kx x l r) = match (compare ky kx) {refl}
  where
    match : (o : Ordering) → {eq : compare ky kx ≡ o} → Map k a {min lower [ ky ]} {max upper [ ky ]}
    match LT {eq} = helper
                    {≤-max [ kx ] [ ky ] (compareLT-≤ ky kx eq)}
                    {≤-max upper [ ky ] (≤-trans {x = [ ky ]} {y = [ kx ]} {z = upper} (compareLT-≤ ky kx eq) (UBisHigher m {refl}))}
      where
        l' = insert ky y l
        helper : {max [ kx ] [ ky ] ≡ [ kx ]} → {max upper [ ky ] ≡ upper}
                → Map k a {min lower [ ky ]} {max upper [ ky ]}
        helper {prf1} {prf2} = balance {l1 = min lower [ ky ]} {u1 = [ kx ]}
                                {l2 = [ kx ]} {u2 = max upper [ ky ]}
                                kx x {{ ≤-refl {x = [ kx ]} }} {{≤-refl {x = [ kx ]}}} (subUpperBound l' {prf1}) (subUpperBound r {sym prf2})

    match GT {eq} = helper
                    {≤-min lower [ ky ] (≤-trans {x = lower} {y = [ kx ]} {z = [ ky ]} (LBisLower m {refl}) (compareGT-≤ ky kx eq))}
                    {≤-min [ kx ] [ ky ] (compareGT-≤ ky kx eq)}
      where
        r' = insert ky y r
        helper : {min lower [ ky ] ≡ lower} → {min [ kx ] [ ky ] ≡ [ kx ]}
                → Map k a {min lower [ ky ]} {max upper [ ky ]}
        helper {prf1} {prf2} = balance {l1 = min lower [ ky ]} {u1 = [ kx ]}
                                {l2 = [ kx ]} {u2 = max upper [ ky ]}
                                kx x {{≤-refl {x = [ kx ]}}} {{≤-refl {x = [ kx ]}}} (subLowerBound l {sym prf1}) (subLowerBound r' {prf2})

    match EQ {eq} = helper {compareEQ-≡ ky kx eq}
                           {≤-min lower [ ky ] (≤-trans {x = lower} {y = [ kx ]} {z = [ ky ]} (LBisLower m {refl}) (EQ-≤ kx ky (sym (compareEQ-≡ ky kx eq))))}
                           {≤-max upper [ ky ] (≤-trans {x = [ ky ]} {y = [ kx ]} {z = upper} ((EQ-≤ ky kx (compareEQ-≡ ky kx eq))) (UBisHigher m {refl}))}
      where
        helper : { ky ≡ kx } → {min lower [ ky ] ≡ lower } → {max upper [ ky ] ≡ upper }
          → Map k a {min lower [ ky ]} {max upper [ ky ]}
        helper {refl} {prf1} {prf2} = subUpperBound (subLowerBound (Bin sz ky y l r)  {sym prf1}) {sym prf2}
