module Data.Map.ListConversionLaws where

open import Haskell.Prelude

open import Data.Map.Internal

open import Data.Utils.Reasoning



emptyListConcatenation : {a : Set} → (xs : List a)
  → xs ++ [] ≡ xs
emptyListConcatenation [] = refl
emptyListConcatenation (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨ cong (x ∷_) (emptyListConcatenation xs) ⟩
    (x ∷ xs)
  ∎

foldrWithKeyBaseConcatenation : {k a b : Set} {{_ : Ord k}}
  → (m : Map k a) (ys zs : List (k × a))
  → let f = (λ k x xs -> (k , x) ∷ xs)
    in (foldrWithKey f ys m) ++ zs ≡ (foldrWithKey f (ys ++ zs) m)
foldrWithKeyBaseConcatenation Tip ys zs = refl
foldrWithKeyBaseConcatenation (Bin sz kx x l r) ys zs =
  let f = (λ k x xs -> (k , x) ∷ xs) in
  begin
    (foldrWithKey f ys (Bin sz kx x l r)) ++ zs
  ≡⟨⟩
    (foldrWithKey f ((kx , x) ∷ (foldrWithKey f ys r)) l) ++ zs
  ≡⟨ foldrWithKeyBaseConcatenation l ((kx , x) ∷ (foldrWithKey f ys r)) zs ⟩
    (foldrWithKey f ((kx , x) ∷ (foldrWithKey f ys r) ++ zs) l)
  ≡⟨ cong (λ t → foldrWithKey f ((kx , x) ∷ t) l) (foldrWithKeyBaseConcatenation r ys zs) ⟩
   (foldrWithKey f ((kx , x) ∷ (foldrWithKey f (ys ++ zs) r)) l)
  ≡⟨⟩
    (foldrWithKey f (ys ++ zs) (Bin sz kx x l r))
  ∎


toAscListRewrite : {k a : Set} {{_ : Ord k}}
  → (sz : Nat) (kx : k) (x : a) (l r : Map k a)
  → (toAscList (Bin sz kx x l r)) ≡ (toAscList l) ++ ((kx , x) ∷ []) ++ (toAscList r)
toAscListRewrite sz kx x l r =
  let f = (λ k x xs -> (k , x) ∷ xs) in
  begin
    toAscList (Bin sz kx x l r)
  ≡⟨⟩
    foldrWithKey f [] (Bin sz kx x l r)
  ≡⟨⟩
    foldrWithKey f ((kx , x) ∷ (foldrWithKey f [] r)) l
  ≡⟨ sym (foldrWithKeyBaseConcatenation l [] ((kx , x) ∷ (foldrWithKey f [] r))) ⟩
    (foldrWithKey f [] l) ++ ((kx , x) ∷ (foldrWithKey f [] r))
  ≡⟨⟩
    (foldrWithKey f [] l) ++ ((kx , x) ∷ []) ++ (foldrWithKey f [] r)
  ≡⟨⟩
    (toAscList l) ++ ((kx , x) ∷ []) ++ (toAscList r)
  ∎




toAscListRoundtrip : {k a : Set} {{_ : Ord k}}
  → (m : Map k a) → fromDistinctAscList (toAscList m) ≡ m
toAscListRoundtrip Tip = refl
toAscListRoundtrip (Bin sz kx x l r) =
  let f = (λ k x xs -> (k , x) ∷ xs) in
  begin
    fromDistinctAscList (toAscList (Bin sz kx x l r))
  ≡⟨ cong (λ t → fromDistinctAscList t) (toAscListRewrite sz kx x l r) ⟩
    fromDistinctAscList ((toAscList l) ++ ((kx , x) ∷ []) ++ (toAscList r))
  ≡⟨ {!   !} ⟩ --TBD
    {!  !}
  ≡⟨⟩
    (Bin sz kx x l r)
  ∎
