module Data.Map.TypeclassLaws.Traversable where

open import Haskell.Prelude hiding (map)

open import Data.Map.Internal.Datatype
open import Data.Map.Internal.Instances

open import Data.Map.Internal.Mapping

open import Data.Utils.Applicative
open import Data.Utils.Identity
open import Data.Utils.Compose

open import Data.Utils.Reasoning


traverseNaturalityMap : {k a b : Set} {{_ : Ord k}}
    → {p q : Set → Set} {{ap : Applicative p}} {{aq : Applicative q}}
    → (f : a → p b) → (t : {x : Set} → p x → q x) → (m : Map k a)
    → (t ∘ traverse f) m ≡ traverse (t ∘ f) m
traverseNaturalityMap f t Tip = begin
    t (traverse f Tip)
  ≡⟨⟩
    t (pure Tip)
  ≡⟨ preservePure Tip ⟩
    pure Tip
  ≡⟨⟩
    traverse (t ∘ f) Tip
  ∎
  where
    postulate
      preservePure : {A : Set} → (a : A) → t (pure a) ≡ pure a

traverseNaturalityMap {p = p} {q = q} {{ap = ap}} {{aq = aq}} f t (Bin sz kx x l r) = begin
    t (traverse f (Bin sz kx x l r))
  ≡⟨⟩
    t (liftA3 (flip (Bin sz kx)) (traverseWithKey (λ _ → f) l) (f x) (traverseWithKey (λ _ → f) r))
  ≡⟨⟩
    t (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l) <*> (f x) <*> (traverseWithKey (λ _ → f) r))

  ≡⟨ preserveApp (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l) <*> (f x)) (traverseWithKey (λ _ → f) r) ⟩
    t (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l) <*> (f x)) <*> t (traverseWithKey (λ _ → f) r)

  ≡⟨ cong (λ tr → t (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l) <*> (f x)) <*> tr) (traverseNaturalityMap f t r) ⟩
    t (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l) <*> (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)

  ≡⟨ cong (λ fst → fst <*> (traverseWithKey (λ _ → t ∘ f) r)) (preserveApp (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l)) (f x)) ⟩
    t (pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → f) l)) <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)

  ≡⟨ cong (λ fst → fst <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)) (preserveApp (pure (flip (Bin sz kx))) (traverseWithKey (λ _ → f) l)) ⟩
    t (pure (flip (Bin sz kx))) <*> t (traverseWithKey (λ _ → f) l) <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)

  ≡⟨ cong (λ tl → t (pure (flip (Bin sz kx))) <*> tl <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)) (traverseNaturalityMap f t l) ⟩
    t (pure (flip (Bin sz kx))) <*> (traverseWithKey (λ _ → t ∘ f) l) <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)

  ≡⟨ cong (λ fst → fst <*> (traverseWithKey (λ _ → t ∘ f) l) <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)) (preservePure (flip (Bin sz kx))) ⟩
    pure (flip (Bin sz kx)) <*> (traverseWithKey (λ _ → t ∘ f) l) <*> (t (f x)) <*> (traverseWithKey (λ _ → t ∘ f) r)

  ≡⟨⟩
    liftA3 (flip (Bin sz kx)) (traverseWithKey (λ _ → t ∘ f) l) (t (f x)) (traverseWithKey (λ _ → t ∘ f) r)
  ≡⟨⟩
    traverse (t ∘ f) (Bin sz kx x l r)
  ∎
  where
    postulate
      preservePure : {A : Set} → (a : A) → t (pure a) ≡ pure a
      preserveApp : {A B : Set} → (g : p (A → B)) (a : p A) → t (g <*> a) ≡ (t g <*> t a)



traversePurityMap : {k a : Set} {{_ : Ord k}}
    → {p : Set → Set} {{ap : Applicative p}}
    → (m : Map k a) → traverse (pure {p}) m ≡ pure m
traversePurityMap Tip = refl
traversePurityMap {p = p} (Bin sz kx x l r) =
  begin
    traverse (pure {p}) (Bin sz kx x l r)
  ≡⟨⟩
    pure (flip (Bin sz kx)) <*> (traverseWithKey tf l) <*> (pure x) <*> (traverseWithKey tf r)

  ≡⟨ cong (λ tl → pure (flip (Bin sz kx)) <*> tl <*> (pure x) <*> (traverseWithKey tf r)) (traversePurityMap {p = p} l) ⟩
    pure (flip (Bin sz kx)) <*> (pure l) <*> (pure x) <*> (traverseWithKey tf r)

  ≡⟨ cong (λ tr → pure (flip (Bin sz kx)) <*> (pure l) <*> (pure x) <*> tr) (traversePurityMap {p = p} r) ⟩
    pure (flip (Bin sz kx)) <*> (pure l) <*> (pure x) <*> (pure r)

  ≡⟨ cong (λ y → y <*> (pure x) <*> (pure r)) (applicativeHomomorphism {p = p} (flip (Bin sz kx)) (l)) ⟩
    pure (flip (Bin sz kx) l) <*> pure x <*> pure r

  ≡⟨ cong (λ y → y <*> pure r) (applicativeHomomorphism {p = p} (flip (Bin sz kx) l) (x)) ⟩
    pure (Bin sz kx x l) <*> pure r

  ≡⟨ applicativeHomomorphism {p = p} (Bin sz kx x l) r ⟩
    pure (Bin sz kx x l r)
  ∎
  where
    tf = (λ _ → pure {p})



traverseIdentityMap : {k a : Set} {{_ : Ord k}}
    → (m : Map k a) → traverse IdentityCon m ≡ IdentityCon m
traverseIdentityMap Tip = refl
traverseIdentityMap (Bin sz kx x l r) = let tf = (λ _ → IdentityCon) in
  begin
    traverse IdentityCon (Bin sz kx x l r)
  ≡⟨⟩
    traverseWithKey tf (Bin sz kx x l r)
  ≡⟨⟩
    pure (flip (Bin sz kx)) <*> (traverseWithKey tf l) <*> (IdentityCon x) <*> (traverseWithKey tf r)
  ≡⟨⟩
    IdentityCon (flip (Bin sz kx)) <*> (traverseWithKey tf l) <*> (IdentityCon x) <*> (traverseWithKey tf r)

  ≡⟨ cong (λ tr → IdentityCon (flip (Bin sz kx)) <*> (traverseWithKey tf l) <*> (IdentityCon x) <*> tr) (traverseIdentityMap r) ⟩
    IdentityCon (flip (Bin sz kx)) <*> (traverseWithKey tf l) <*> (IdentityCon x) <*> (IdentityCon r)

  ≡⟨ cong (λ tl → IdentityCon (flip (Bin sz kx)) <*> tl <*> (IdentityCon x) <*> (IdentityCon r)) (traverseIdentityMap l) ⟩
    IdentityCon (flip (Bin sz kx)) <*> (IdentityCon l) <*> (IdentityCon x) <*> (IdentityCon r)

  ≡⟨⟩
    IdentityCon (Bin sz kx x l r)
  ∎



traverseCompositionMap : {k a b c : Set} {{_ : Ord k}}
    → {p q : Set → Set} {{ap : Applicative p}} {{aq : Applicative q}}
    → (g : b → q c) (f : a → p b) (m : Map k a)
    → traverse (ComposeCon ∘ fmap g ∘ f) m ≡ (ComposeCon ∘ fmap (traverse g) ∘ traverse f) m
traverseCompositionMap {p = p} {q = q} g f Tip = begin
    traverse (ComposeCon ∘ fmap g ∘ f) Tip
  ≡⟨⟩
    pure Tip
  ≡⟨⟩
    ComposeCon (pure (pure Tip))

  ≡⟨ cong (λ y → ComposeCon (pure y)) (sym (traversePurityMap {p = q} Tip)) ⟩
    ComposeCon (pure (traverse pure Tip))

  ≡⟨ cong (λ y → ComposeCon y) (sym (applicativeHomomorphism (traverse g) Tip)) ⟩
    ComposeCon (pure (traverse g) <*> pure Tip)

  ≡⟨ cong (λ y → ComposeCon y) (sym (applicativeFunctorLaw (traverse g) (pure Tip))) ⟩
    ComposeCon (fmap (traverse g) (pure Tip))
  ≡⟨⟩
    ComposeCon (fmap (traverse g) (traverse f Tip))
  ∎

traverseCompositionMap {p = p} {q = q} g f (Bin sz kx x l r) =
  begin
    traverse (ComposeCon ∘ fmap g ∘ f) (Bin sz kx x l r)
  ≡⟨⟩
    pure (flip (Bin sz kx)) <*> (traverse (ComposeCon ∘ fmap g ∘ f) l) <*> (ComposeCon (fmap g (f x))) <*> (traverse (ComposeCon ∘ fmap g ∘ f) r)

  ≡⟨ cong (λ tl → pure (flip (Bin sz kx)) <*> tl <*> (ComposeCon (fmap g (f x))) <*> (traverse (ComposeCon ∘ fmap g ∘ f) r)) (traverseCompositionMap g f l) ⟩
    pure (flip (Bin sz kx)) <*> (ComposeCon (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (traverse (ComposeCon ∘ fmap g ∘ f) r)

  ≡⟨ cong (λ tr → pure (flip (Bin sz kx)) <*> (ComposeCon (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> tr) (traverseCompositionMap g f r) ⟩
    pure (flip (Bin sz kx)) <*> (ComposeCon (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))
  ≡⟨⟩
    ComposeCon (pure (pure (flip (Bin sz kx)))) <*> (ComposeCon (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))
  ≡⟨⟩
    ComposeCon ( pure (_<*>_) <*> (pure (pure (flip (Bin sz kx)))) <*> (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))

  ≡⟨ cong (λ y → ComposeCon (y <*> (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))) (applicativeHomomorphism {p = p} (_<*>_) (pure (flip (Bin sz kx))) ) ⟩
    ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (fmap (traverse g) (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))

  ≡⟨ cong (λ y → ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> y) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))) (applicativeFunctorLaw (traverse g) (traverse f l)) ⟩
    ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (pure (traverse g) <*> (traverse f l))) <*> (ComposeCon (fmap g (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))

  ≡⟨ cong (λ y → ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (pure (traverse g) <*> (traverse f l))) <*> (ComposeCon y) <*> (ComposeCon (fmap (traverse g) (traverse f r)))) (applicativeFunctorLaw g (f x)) ⟩
    ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (pure (traverse g) <*> (traverse f l))) <*> (ComposeCon (pure g <*> (f x))) <*> (ComposeCon (fmap (traverse g) (traverse f r)))

  ≡⟨ cong (λ y → ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (pure (traverse g) <*> (traverse f l))) <*> (ComposeCon (pure g <*> (f x))) <*> (ComposeCon y)) (applicativeFunctorLaw (traverse g) (traverse f r)) ⟩
    ComposeCon ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (pure (traverse g) <*> (traverse f l))) <*> (ComposeCon (pure g <*> (f x))) <*> (ComposeCon (pure (traverse g) <*> (traverse f r)))
  ≡⟨⟩
    ComposeCon (pure (_<*>_) <*> (pure (_<*>_) <*> ((pure (pure (flip (Bin sz kx)) <*>_)) <*> (pure (traverse g) <*> (traverse f l))) <*> (pure g <*> (f x))) <*> (pure (traverse g) <*> (traverse f r)))

  ≡⟨ {! !} ⟩
    ComposeCon (pure (traverse g) <*> (pure (flip (Bin sz kx)) <*> (traverse f l) <*> (f x) <*> (traverse f r)) )
  ≡⟨⟩
    ComposeCon (pure (traverse g) <*> (traverse f (Bin sz kx x l r)))

  ≡⟨ cong (λ y → ComposeCon y) (sym (applicativeFunctorLaw (traverse g) (traverse f (Bin sz kx x l r)))) ⟩
    ComposeCon (fmap (traverse g) (traverse f (Bin sz kx x l r)))
  ∎
