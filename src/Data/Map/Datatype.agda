module Data.Map.Datatype where


open import Haskell.Prelude

open import Data.Utils.PartialOrder

open Data.Utils.PartialOrder public

{-------------------
  Map
-------------------}


data Map (k : Set) (a : Set) ⦃ kOrd : Ord k ⦄ {lower upper : [ k ]∞} : Set

size : {k a : Set} → ∀ {lower upper : [ k ]∞} → ⦃ _ : Ord k ⦄
       → Map k a { lower } { upper } → Nat


data Map k a ⦃ kOrd ⦄ {lower} {upper} where

  Bin : (sz : Nat) → (kx : k) → (x : a)
        → (l : Map k a {lower} {[ kx ]}) → (r : Map k a {[ kx ]} {upper})
        → {{_ : sz ≡ (size l) + (size r) + 1}}
        → Map k a {lower} {upper}

  Tip : ⦃ l≤u : lower ≤ upper ⦄ → Map k a
{-# COMPILE AGDA2HS Map #-}


size Tip = 0
size (Bin sz _ _ _ _) = sz
{-# COMPILE AGDA2HS size #-}

rebound : {k a : Set} {{_ : Ord k}} {lower upper : [ k ]∞} → Map k a {lower} {upper} → Map k a { -∞} { +∞}
rebound Tip = Tip {{l≤u = refl}}
rebound {k} {a} {{iOrdk}} {lower} {upper} t@(Bin sz kx x l r)
    = let l' = (rebound' {newLower =   -∞  } {newUpper = [ kx ]} {{refl}} {{[]-≤-I {A = k} {{x≤y = ≤-refl {A = [ k ]∞}}} }}   l )
          r' = (rebound' {newLower = [ kx ]} {newUpper =   +∞  } {{[]-≤-I {A = k} {{x≤y = ≤-refl {A = [ k ]∞}}}}} {{+∞-≤-I {A = k} {x = upper}}}  r )
      in Bin (size l' + size r' + 1) kx x l' r'
  where
    rebound' : {k a : Set} {{_ : Ord k}} {lower upper : [ k ]∞}
              → {newLower newUpper : [ k ]∞} {{nl≤l : newLower ≤ lower}} {{u≤nu : upper ≤ newUpper}}
              → Map k a {lower} {upper} → Map k a {newLower} {newUpper}

    rebound' {k} {a} {{iOrdk}} {lower} {upper} {nl} {nu} {{nl≤l}} {{u≤nu}} (Tip {{l≤u = l≤u}}) =
        Tip {{l≤u = ≤-trans {A = [ k ]∞} {x = nl} {y = upper} (≤-trans {A = [ k ]∞} {x = nl} {y = lower} {z = upper} nl≤l l≤u) u≤nu}}

    rebound' {k} {a} {{iOrdk}} {lower} {upper} {nl} {nu} {{nl≤l}} {{u≤nu}} t@(Bin sz kx x l r) =
        let l' = (rebound' {newLower =   nl  } {newUpper = [ kx ]} {{nl≤l = nl≤l}} {{u≤nu = []-≤-I {A = k} {{x≤y = ≤-refl {A = [ k ]∞}}} }}  l )
            r' = (rebound' {newLower = [ kx ]} {newUpper =   nu  } {{nl≤l = []-≤-I {A = k} {{x≤y = ≤-refl {A = [ k ]∞}}} }} {{u≤nu = u≤nu}}  r )
        in Bin (size l' + size r' + 1) kx x l' r'
