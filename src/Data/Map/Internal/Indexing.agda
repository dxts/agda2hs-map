{-# OPTIONS --warning noMissingDefinitions #-}
{-# OPTIONS --show-implicit #-}

module Data.Map.Internal.Indexing where

open import Haskell.Prelude
    hiding (take; drop; splitAt)
{-# FOREIGN AGDA2HS
import Prelude hiding (take, drop, splitAt)
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

open import Data.Map.Internal.Linking
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Linking
#-}

open import Data.Map.Internal.Balancing
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Balancing
#-}

open import Data.Map.PreconditionProofs


module Indexing {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  findIndex : ∀ {lower upper : [ k ]∞} → (key : k) → (map : Map k a {lower} {upper}) → {key ∈ map} → Nat
  findIndex = go 0
    where
      go : ∀ {lower upper : [ k ]∞} → Nat → (key : k) → (map : Map k a {lower} {upper}) → {key ∈ map} → Nat
      go _   _ Tip  = error "Map.findIndex: element is not in the map"
      go idx key (Bin sz kx x l r {{szVal}}) {prf} = match (compare key kx) {refl}
        where
          match : (o : Ordering) → {eq : compare key kx ≡ o} → Nat
          match LT {eq} = go idx key l {∈L sz key kx x l r szVal eq prf}
          match GT {eq} = go (idx + (size l) + 1) key r {∈R sz key kx x l r szVal eq prf}
          match EQ {eq} = idx + (size l)
  {-# COMPILE AGDA2HS findIndex #-}

  lookupIndex : ∀ {lower upper : [ k ]∞} → k → Map k a {lower} {upper} → Maybe Nat
  lookupIndex = go 0
    where
      go : ∀ {lower upper : [ k ]∞} → Nat → k → Map k a → Maybe Nat
      go _   _ Tip              = Nothing
      go idx k (Bin _ kx _ l r) = let sizeL = size l
        in case (compare k kx) of
          λ {
            LT → go idx k l
          ; GT → go (idx + sizeL + 1) k r
          ; EQ → Just (idx + sizeL)
          }
  {-# COMPILE AGDA2HS lookupIndex #-}

  elemAt : ∀ {lower upper : [ k ]∞} → (n : Nat) → (map : Map k a {lower} {upper}) → { (n < (size map)) ≡ true } → k × a
  elemAt _ Tip = error "Map.elemAt: index out of range"
  elemAt i (Bin sz kx x l r {{szVal}}) {iVal} = match (compare i sizeL) {refl}
    where
      sizeL = (size l)
      match : (o : Ordering) → {eq : compare i sizeL ≡ o} → k × a
      match LT {eq} = elemAt i l {∈[L] i l eq}
      match GT {eq} = elemAt (_-_ (_-_ i sizeL {{gtRewrite1 i sizeL eq}}) 1 {{gtRewrite2 i sizeL eq}}) r {∈[R] i sz kx x l r szVal iVal eq }
      match EQ {eq} = (kx , x)
  {-# COMPILE AGDA2HS elemAt #-}

  take : ∀ {lower upper : [ k ]∞} → Nat → Map k a {lower} {upper} → Map k a { -∞ } { +∞ }
  take _ Tip = Tip
  take i m@(Bin _ kx x l r) = let sizeL = size l in
    if (i >= size m)
    then rebound m
    else (if i <= 0
          then Tip
          else (case (compare i sizeL) of
                λ {
                  LT → take i l
                ; GT → rebound (link kx x l (take (i - sizeL - 1) r))
                ; EQ → rebound l
                }))
  {-# COMPILE AGDA2HS take #-}

  drop : Nat → Map k a → Map k a
  drop _ Tip = Tip
  drop i m@(Bin _ kx x l r) = let sizeL = size l in
    if i >= size m
    then Tip
    else (if i <= 0
          then m
          else (case (compare i sizeL) of
                λ {
                  LT → link kx x (drop i l) r
                ; GT → drop (i - sizeL - 1) r
                ; EQ → insertMin kx x r
                }))
  {-# COMPILE AGDA2HS drop #-}

  splitAt : Nat → Map k a → (Map k a × Map k a)
  splitAt _ Tip = Tip , Tip
  splitAt i m@(Bin _ kx x l r) = let sizeL = size l in
    if i >= size m
    then (m , Tip)
    else (if i <= 0
          then (Tip , m)
          else (case (compare i sizeL) of
                λ {
                  LT → case (splitAt i l) of λ { (ll , lr) → ll , link kx x lr r }
                ; GT → case (splitAt (i - sizeL - 1) r) of λ { (rl , rr) → link kx x l rl , rr }
                ; EQ → l , insertMin kx x r
                }))
  {-# COMPILE AGDA2HS splitAt #-}

  updateAt : (k → a → Maybe a) → (n : Nat) → (map : Map k a) → {(n <= size map) ≡ true} → Map k a
  updateAt f i Tip = error "Map.updateAt: index out of range"
  updateAt f i (Bin sz kx x l r) = match (compare i sizeL) {refl}
    where
      sizeL = (size l)
      match : (o : Ordering) → {eq : compare i sizeL ≡ o} → Map k a
      match LT {eq} = balanceR kx x (updateAt f i l {∈[L] i l eq}) r
      match GT {eq} = balanceL kx x l (updateAt f (i - sizeL - 1)
                                        r { ∈[R] i l r eq } )
      match EQ {eq} = case (f kx x) of
        λ {
          (Just x') → Bin sz kx x' l r
        ; Nothing → glue l r
        }
  {-# COMPILE AGDA2HS updateAt #-}

  deleteAt : (n : Nat) → (map : Map k a) → {(n <= size map) ≡ true} → Map k a
  deleteAt i Tip = error "Map.updateAt: index out of range"
  deleteAt {k} {a} i (Bin sz kx x l r) = match (compare i sizeL) {refl}
    where
      sizeL = (size l)
      match : (o : Ordering) → {eq : compare i sizeL ≡ o} → Map k a
      match LT {eq} = balanceR kx x (deleteAt i l {∈[L] i l eq}) r
      match GT {eq} = balanceL kx x l (deleteAt (i - sizeL - 1)
                                        r { ∈[R] i l r eq } )
      match EQ {eq} = glue l r
  {-# COMPILE AGDA2HS deleteAt #-}


open Indexing public
