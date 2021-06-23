module Data.Map.PreconditionProofs where

open import Haskell.Prelude

open import Data.Map.Internal.Datatype

open import Data.Utils.Reasoning

{---------------------------}
open import Agda.Builtin.Reflection

{- Default value tactic for implicit arguments -}
defaultTo : {A : Set} (x : A) → Term → TC ⊤
defaultTo x hole = bindTC (quoteTC x) (unify hole)
{---------------------------}


postulate
  ltRewrite1 : (x y : Nat) → (prf : compare x y ≡ LT)
          → IsFalse (y < x)
  ltRewrite2 : (x y : Nat) → (prf : compare x y ≡ LT)
          → (x < y) ≡ true

  gtRewrite1 : (x y : Nat) → (prf : compare x y ≡ GT)
          → IsFalse (x < y)
  gtRewrite2 : (x y : Nat) → (prf : compare x y ≡ GT)
          → IsFalse ((_-_ x y {{gtRewrite1 x y prf}}) < 1)


{- Nat subtraction -}
subtract : (x y z : Nat) → {_ : compare x y ≡ GT} {@(tactic defaultTo {x ≡ x} refl) _ : z ≡ 1} → Nat
subtract x y z {eq} {_} = _-_ (_-_ x y {{gtRewrite1 x y eq}}) 1 {{gtRewrite2 x y eq}}


module Precondition {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  {--------------------
    Functions to enforce preconditions
  --------------------}

  -- data _∈_ {k a : Set} : k → Map k a → Set where
  --   here : (sz : Nat) -> (kx : k) (x : a) -> (l r : Map k a) -> (szVal : sz ≡ (size l) + (size r) + 1)
  --         -> kx ∈ (Bin sz kx x l r)

  _∈_ : (key : k) → Map k a → Set
  _ ∈ Tip = ⊥
  k ∈ (Bin _ kx _ l r) with (compare k kx)
  ... | LT = k ∈ l
  ... | GT = k ∈ r
  ... | EQ = ⊤


  {--------------------
    Functions to transform proofs, eg : shrinking pre-condition proofs
  --------------------}


  ∈L :  (sz : Nat) (key kx : k) (x : a)
            → (l : Map k a ) (r : Map k a )
            → (eq : compare key kx ≡ LT)
            → (prf : key ∈ (Bin sz kx x l r))
            → (key ∈ l)
  ∈L sz key kx x l r eq prf with (compare key kx)
  ... | LT = prf


  ∈R :  (sz : Nat) (key kx : k) (x : a)
            → (l : Map k a ) (r : Map k a )
            → (eq : compare key kx ≡ GT)
            → (prf : key ∈ (Bin sz kx x l r))
            → (key ∈ r)
  ∈R sz key kx x l r eq prf with compare key kx
  ... | GT = prf


  ∈[L] :  (n : Nat) (l : Map k a)
          → (eq : compare n (size l) ≡ LT)
          → (n < (size l)) ≡ true
  ∈[L] n l eq = ltRewrite2 n (size l) eq

  postulate
    ∈[R] :  (n sz : Nat) (l : Map k a ) (r : Map k a )
          → (nValid :  (n < sz) ≡ true)
          → (eq : compare n (size l) ≡ GT)
          → ((subtract n (size l) 1 {eq} {refl}) < size r) ≡ true
  -- ∈[R] n sz kx x l r {nValid} eq {nLB} {nLB2} with (compare n (size l))
  -- ... | GT = {!   !}

open Precondition public
