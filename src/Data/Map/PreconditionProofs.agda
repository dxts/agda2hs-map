module Data.Map.PreconditionProofs where

open import Haskell.Prelude

open import Data.Map.Datatype

open import Data.Utils.Reasoning
open import Data.Utils.IntegerProofs



postulate
  ltRewrite1 : (x y : Nat) → (prf : compare x y ≡ LT)
          → IsFalse (y < x)
  ltRewrite2 : (x y : Nat) → (prf : compare x y ≡ LT)
          → (x < y) ≡ true

  gtRewrite1 : (x y : Nat) → (prf : compare x y ≡ GT)
          → IsFalse (x < y)
  gtRewrite2 : (x y : Nat) → (prf : compare x y ≡ GT)
          → IsFalse ((_-_ x y {{gtRewrite1 x y prf}}) < 1)

module Precondition {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  {--------------------
    Functions to enforce preconditions
  --------------------}

  _∈_ : ∀ {lower upper : [ k ]∞} → (key : k)
        → Map k a { lower } { upper } → Set
  _ ∈ Tip = ⊥
  k ∈ (Bin _ kx _ l r) with (compare k kx)
  ... | LT = k ∈ l
  ... | GT = k ∈ r
  ... | EQ = ⊤


  -- data [_]∈_ {lower upper : [ k ]∞} (n : Nat) :
  --         Map k a { lower } { upper } → Set where
  --   here : n → (kx : k) (x : a) (l : Map k a {lower} {[ kx ]})
  --         (r : Map k a {[ kx ]} {[ upper ]}) → [ n ]∈ (Bin (n + 1) kx x l r)
  -- -- [ n ]∈ Tip = (n > 0) ≡ true
  -- -- [ n ]∈ (Bin sz _ _ l r) with (compare n sz)
  -- -- ... | LT = (n < sz) ≡ true
  -- -- ... | GT = (n > sz) ≡ true
  -- -- ... | EQ = (n == sz) ≡ true



  {--------------------
    Functions to transform proofs, eg : shrinking pre-condition proofs
  --------------------}


  ∈L : ∀ {lower upper : [ k ]∞}
            → (sz : Nat) (key kx : k) (x : a)
            → (l : Map k a {lower} {[ kx ]}) (r : Map k a {[ kx ]} {upper})
            → (szVal : sz ≡ (size l) + (size r) + 1)
            → (eq : compare key kx ≡ LT)
            → (prf : key ∈ (Bin sz kx x l r {{szVal}}))
            → (key ∈ l)
  ∈L sz key kx x l r szVal eq prf with (compare key kx)
  ... | LT = prf


  ∈R : ∀ {lower upper : [ k ]∞}
            → (sz : Nat) (key kx : k) (x : a)
            → (l : Map k a {lower} {[ kx ]}) (r : Map k a {[ kx ]} {upper})
            → (szVal : sz ≡ (size l) + (size r) + 1)
            → (eq : compare key kx ≡ GT)
            → (prf : key ∈ (Bin sz kx x l r {{szVal}}))
            → (key ∈ r)
  ∈R sz key kx x l r szVal eq prf with compare key kx
  ... | GT = prf


  ∈[L] : ∀ {lower upper : [ k ]∞}
          → (n : Nat) (l : Map k a {lower} {upper})
          → (eq : compare n (size l) ≡ LT)
          → (n < (size l)) ≡ true
  ∈[L] n l eq = ltRewrite2 n (size l) eq

  postulate
    ∈[R] : ∀ {lower upper : [ k ]∞}
          → (n sz : Nat) (kx : k) (x : a) (l : Map k a {lower} {[ kx ]}) (r : Map k a {[ kx ]} {upper})
          (szVal : sz ≡ (size l) + (size r) + 1) (nValid :  (n < sz) ≡ true)
          → (eq : compare n (size l) ≡ GT)
          → {nLB : IsFalse (n < size l)} {nLB2 : IsFalse ((_-_ n (size l) {{nLB}}) < 1)}
          → ((_-_ (_-_ n  (size l) {{nLB}}) 1 {{nLB2}}) < size r) ≡ true
  -- ∈[R] n sz kx x l r szVal {nValid} eq {nLB} {nLB2} with (compare n (size l))
  -- ... | GT = {!   !}

open Precondition public
