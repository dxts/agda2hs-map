module Data.Map.Internal where


open import Haskell.Prelude
    hiding (lookup; map; filter; foldr; foldl; null; splitAt; take; drop)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup, map, filter, foldr, foldl, null, splitAt, take, drop)
#-}

open import Data.Sett.Internal
{-# FOREIGN AGDA2HS
import qualified Data.Set.Internal as Set
#-}

open import Data.Map.Utils

{-------------------
  Map
-------------------}

data Map (k : Set) (a : Set) : Set  where
  Bin : (size : Int) → (kx : k) → (x : a) → (l : Map k a) → (r : Map k a) → Map k a
  Tip : Map k a
{-# COMPILE AGDA2HS Map #-}


{--------------------------------------------------------------------------
  All type definitions have been hoisted to the top to allow mutual recursion
  while still maintaining the order of definition of functions from the library.
--------------------------------------------------------------------------}


{-------------------
  Query
-------------------}

null : {k a : Set} → Map k a → Bool

size : {k a : Set} → Map k a → Int

lookup : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe a

member : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Bool

notMember : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Bool

find : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → a

findWithDefault : {k a : Set} → ⦃ Ord k ⦄ → a → k → Map k a → a

lookupLT : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)

lookupGT : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)

lookupLE : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)

lookupGE : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)

{-------------------
  Operators
-------------------}

_!_ :  {k a : Set} → ⦃ kOrd : Ord k ⦄ → (map : Map k a) → (key : k) → {Holds (member ⦃ kOrd ⦄ key map)} → a

_!?_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a → k → Maybe a

_\\_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Map k a


{-------------------
  Construction
-------------------}

empty : {k a : Set} → Map k a

singleton : {k a : Set} → k → a → Map k a

{-------------------
  Insertion
-------------------}

insert : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a

insertR : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a

insertWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a

insertWithR : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a

insertWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a

insertWithKeyR : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a

insertLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → (Maybe a × Map k a)


{-------------------
  Deletion
-------------------}

delete : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq (Map k a) ⦄ → k → Map k a → Map k a

adjust : {k a : Set} → ⦃ Ord k ⦄ → (a → a) → k → Map k a → Map k a

adjustWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a) → k → Map k a → Map k a

update : {k a : Set} → ⦃ Ord k ⦄ → (a → Maybe a) → k → Map k a → Map k a

updateWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → Map k a

updateLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → (Maybe a × Map k a)

alter : {k a : Set} → ⦃ Ord k ⦄ → (Maybe a → Maybe a) → k → Map k a → Map k a

-- [TODO] `alterF` and related methods


{-------------------
  Indexing
-------------------}

findIndex : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → Int

lookupIndex : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe Int

elemAt : {k a : Set} → (n : Int) → (map : Map k a) → {Holds ((size map) > 0)} → k × a

take : {k a : Set} →  Int → Map k a → Map k a

drop : {k a : Set} →  Int → Map k a → Map k a

splitAt : {k a : Set} →  Int → Map k a → (Map k a × Map k a)

updateAt : {k a : Set} → (k → a → Maybe a) → Int → (map : Map k a) → {Holds ((size map) > 0)} → Map k a

deleteAt : {k a : Set} → Int → (map : Map k a) → {Holds ((size map) > 0)} → Map k a


{-------------------
  Minimal, Maximal
-------------------}

lookupMinSure : {k a : Set} → k → a → Map k a → k × a

lookupMin : {k a : Set} → Map k a → Maybe (k × a)

findMin : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → k × a

lookupMaxSure : {k a : Set} → k → a → Map k a → k × a

lookupMax : {k a : Set} → Map k a → Maybe (k × a)

findMax : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → k × a

deleteMin : {k a : Set} → Map k a → Map k a

deleteMax : {k a : Set} → Map k a → Map k a

updateMin : {k a : Set} → (a → Maybe a) → Map k a → Map k a

updateMax : {k a : Set} → (a → Maybe a) → Map k a → Map k a

updateMinWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a

updateMaxWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a

minViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)

maxViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)

minView : {k a : Set} → Map k a → Maybe (a × Map k a)

maxView : {k a : Set} → Map k a → Maybe (a × Map k a)


{-------------------
  Union
-------------------}

unions : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → f (Map k a) → Map k a

unionsWith : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → (a → a → a) → f (Map k a) → Map k a

union : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → Map k a → Map k a → Map k a

{-------------------
  Union with a combining function.
-------------------}

unionWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → Map k a → Map k a → Map k a

unionWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → Map k a → Map k a → Map k a

{-------------------
  Difference
-------------------}

difference : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Map k a

withoutKeys : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Sett k → Map k a

differenceWith : {k a : Set} → ⦃ Ord k ⦄ → (a → b → Maybe a) → Map k a → Map k b → Map k a

differenceWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → b → Maybe a) → Map k a → Map k b → Map k a

{-------------------
  Intersection
-------------------}

intersection : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Map k a

restrictKeys : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Sett k → Map k a

intersectionWith : {k a : Set} → ⦃ Ord k ⦄ → (a → b → c) → Map k a → Map k b → Map k c

intersectionWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → b → c) → Map k a → Map k b → Map k c


{-------------------
  Disjoint
-------------------}

disjoint : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Bool


{-------------------
  Compose
-------------------}

compose : ⦃ Ord b ⦄ → Map b c → Map a b → Map a c

{-------------------
  merge
-------------------}

-- [TODO] `merge` function and it's helpers.

mergeWithKey : {k a : Set} → ⦃ Ord b ⦄ → (k → a → b → Maybe c)
             → (Map k a → Map k c) → (Map k b → Map k c)
             → Map k a → Map k b → Map k c


{-------------------
  split
-------------------}

split : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Map k a)

splitLookup : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Maybe a × Map k a)

splitMember : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Bool × Map k a)

{-------------------
  link
-------------------}

link : {k a : Set} → k → a → Map k a → Map k a → Map k a

insertMax : {k a : Set} → k → a → Map k a → Map k a

insertMin : {k a : Set} → k → a → Map k a → Map k a


{-------------------
  link2
-------------------}

link2 : {k a : Set} → Map k a → Map k a → Map k a


{-------------------
  glue
-------------------}

glue : {k a : Set} → Map k a → Map k a → Map k a


data MinView (k : Set) (a : Set) : Set where
  MinViewCon : k → a → (Map k a) → MinView k a

data MaxView (k : Set) (a : Set) : Set where
  MaxViewCon : k → a → (Map k a) → MaxView k a

minViewSure : {k a : Set} → k → a → Map k a → Map k a → MinView k a

maxViewSure : {k a : Set} → k → a → Map k a → Map k a → MaxView k a

deleteFindMin : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → ((k × a) × Map k a)

deleteFindMax : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → ((k × a) × Map k a)


{-------------------
  balance
-------------------}

balance : {k a : Set} → k → a → Map k a → Map k a → Map k a

balanceL : {k a : Set} → k → a → Map k a → Map k a → Map k a

balanceR : {k a : Set} → k → a → Map k a → Map k a → Map k a


{-------------------
  bin
-------------------}

bin : {k a : Set} → k → a → Map k a → Map k a → Map k a


{-------------------
  splitRoot
-------------------}

splitRoot : {k a : Set} → Map k a → List (Map k a)


{--------------------------------------------------------------------------
  Function definitions.
--------------------------------------------------------------------------}

{-------------------
  Query
-------------------}

-- null : {k a : Set} → Map k a → Bool
null Tip = true
null (Bin _ _ _ _ _) = false

-- size : {k a : Set} → Map k a → Int
size Tip = 0
size (Bin sz _ _ _ _) = sz

-- lookup : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe a
lookup k Tip = Nothing
lookup k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT → lookup k l
    ; GT → lookup k r
    ; EQ → Just x
    }

-- member : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Bool
member _ Tip = false
member k (Bin _ kx _ l r) = case (compare k kx) of
    λ {
      LT → member k l
    ; GT → member k r
    ; EQ → true
    }

{- [TODO] Need to show that if key Holds in a map, then it also Holds in either the left or right subtree -}
-- shrinkMembership : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} →
-- shrinkMembership k (Bin _ kx _ l r) = case (compare k kx) of
--     λ {
--       LT → doesHold
--     ; GT → doesHold
--     ; EQ → λ Holds ((member k l) || (member k r))
--     }

-- notMember : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Bool
notMember k m = not (member k m)

-- find : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → a
find _ Tip = error "Map.!: given key is not an element in the map"
find k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT → find k l
    ; GT → find k r
    ; EQ → x
    }

-- findWithDefault : {k a : Set} → ⦃ Ord k ⦄ → a → k → Map k a → a
findWithDefault def _ Tip               = def
findWithDefault def k (Bin _ kx x l r)  = case (compare k kx) of
    λ {
      LT → findWithDefault def k l
    ; GT → findWithDefault def k r
    ; EQ → x
    }

-- lookupLT : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
lookupLT _ Tip              = Nothing
lookupLT k (Bin _ kx x l r) = if k <= kx then (lookupLT k l)
                                         else (goJust k kx x r)
  where
    goJust : {k a : Set} → ⦃ Ord k ⦄ → k → k → a → Map k a → Maybe (k × a)
    goJust _ kx' x' Tip               = Just (kx' , x')
    goJust k kx' x' (Bin _ kx x l r)  = if k <= kx then (goJust k kx' x' l)
                                                   else (goJust k kx x r)

-- lookupGT : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
lookupGT _ Tip              = Nothing
lookupGT k (Bin _ kx x l r) = if k < kx then (goJust k kx x l)
                                        else (lookupGT k r)
  where
    goJust : {k a : Set} → ⦃ Ord k ⦄ → k → k → a → Map k a → Maybe (k × a)
    goJust _ kx' x' Tip               = Just (kx' , x')
    goJust k kx' x' (Bin _ kx x l r)  = if k < kx then (goJust k kx x l)
                                                  else (goJust k kx' x' r)

-- lookupLE : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
lookupLE _ Tip              = Nothing
lookupLE k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT → lookupLE k l
    ; EQ → Just (kx , x)
    ; GT → goJust k kx x r
    }
  where
    goJust : {k a : Set} → ⦃ Ord k ⦄ → k → k → a → Map k a → Maybe (k × a)
    goJust _ kx' x' Tip               = Just (kx' , x')
    goJust k kx' x' (Bin _ kx x l r)  = case (compare k kx) of
        λ {
          LT → goJust k kx' x' l
        ; EQ → Just (kx , x)
        ; GT → goJust k kx x r
        }

-- lookupGE : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
lookupGE _ Tip              = Nothing
lookupGE k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT → goJust k kx x l
    ; EQ → Just (kx , x)
    ; GT → lookupGE k r
    }
  where
    goJust : {k a : Set} → ⦃ Ord k ⦄ → k → k → a → Map k a → Maybe (k × a)
    goJust _ kx' x' Tip               = Just (kx' , x')
    goJust k kx' x' (Bin _ kx x l r)  = case (compare k kx) of
        λ {
          LT → goJust k kx x l
        ; EQ → Just (kx , x)
        ; GT → goJust k kx' x' r
        }


{-------------------
  Operators
-------------------}

-- _!_ :  {k a : Set} → ⦃ kOrd : Ord k ⦄ → (map : Map k a) → (key : k) → {Holds (member ⦃ kOrd ⦄ key map)} → a
_!_ m k {notEmpty} = find k m {notEmpty}

-- _!?_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a -> k -> Maybe a
_!?_ m k = lookup k m

-- _\\_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a -> Map k b -> Map k a
_\\_ m1 m2 = difference m1 m2


{-------------------
  Construction
-------------------}

-- empty : {k a : Set} → Map k a
empty = Tip

-- singleton : {k a : Set} → k → a → Map k a
singleton k x = Bin 1 k x Tip Tip


{-------------------
  Insertion
-------------------}

-- insert : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
insert kx x Tip                 = singleton kx x
insert kx x t@(Bin sz ky y l r) = case (compare kx ky) of
    λ {
      LT → let l' = insert kx x l in if (l' == l) then t else (balanceL ky y l' r)
    ; GT → let r' = insert kx x r in if (r' == r) then t else (balanceR ky y l r')
    ; EQ → if (x == y && kx == ky) then t else (Bin sz kx x l r)
    }

-- insertR : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
insertR kx x Tip                 = singleton kx x
insertR kx x t@(Bin sz ky y l r) = case (compare kx ky) of
    λ {
      LT → let l' = insert kx x l in if (l' == l) then t else (balanceL ky y l' r)
    ; GT → let r' = insert kx x r in if (r' == r) then t else (balanceR ky y l r')
    ; EQ → t
    }

-- insertWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a
insertWith _ kx x Tip               = singleton kx x
insertWith f kx x (Bin sz ky y l r) = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWith f kx x l) r
    ; GT → balanceR ky y l (insertWith f kx x r)
    ; EQ → Bin sz kx (f x y) l r
    }

-- insertWithR : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a
insertWithR _ kx x Tip               = singleton kx x
insertWithR f kx x (Bin sz ky y l r) = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWith f kx x l) r
    ; GT → balanceR ky y l (insertWith f kx x r)
    ; EQ → Bin sz kx (f y x) l r
    }

-- insertWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a
insertWithKey _ kx x Tip                = singleton kx x
insertWithKey f kx x (Bin sz ky y l r)  = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWithKey f kx x l) r
    ; GT → balanceR ky y l (insertWithKey f kx x r)
    ; EQ → Bin sz kx (f kx x y) l r
    }

-- insertWithKeyR : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a
insertWithKeyR _ kx x Tip                = singleton kx x
insertWithKeyR f kx x (Bin sz ky y l r)  = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWithKey f kx x l) r
    ; GT → balanceR ky y l (insertWithKey f kx x r)
    ; EQ → Bin sz kx (f kx y x) l r
    }

-- insertLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → (Maybe a × Map k a)
insertLookupWithKey _ kx x Tip                = (Nothing , singleton kx x)
insertLookupWithKey f kx x (Bin sz ky y l r)  = case (compare kx ky) of
    λ {
      LT → let res = insertLookupWithKey f kx x l
               t' = balanceL ky y (snd res) r
               in (fst res , t')
    ; GT → let res = insertLookupWithKey f kx x r
               t' = balanceR ky y l (snd res)
               in (fst res , t')
    ; EQ → (Just y , Bin sz kx (f kx x y) l r)
    }


{-------------------
  Deletion
-------------------}

-- delete : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq (Map k a) ⦄ → k → Map k a → Map k a
delete _ Tip                = Tip
delete k t@(Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT → let l' = delete k l in if (l' == l) then t else balanceR kx x l' r
    ; GT → let r' = delete k r in if (r' == r) then t else balanceL kx x l r'
    ; EQ → glue l r
    }

-- adjust : {k a : Set} → ⦃ Ord k ⦄ → (a → a) → k → Map k a → Map k a
adjust f = adjustWithKey (λ _ x → f x)

-- adjustWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a) → k → Map k a → Map k a
adjustWithKey _ _ Tip               = Tip
adjustWithKey f k (Bin sz kx x l r) = case (compare k kx) of
    λ {
      LT → Bin sz kx x (adjustWithKey f k l) r
    ; GT → Bin sz kx x l (adjustWithKey f k r)
    ; EQ → Bin sz kx (f kx x) l r
    }


-- update : {k a : Set} → ⦃ Ord k ⦄ → (a → Maybe a) → k → Map k a → Map k a
update f = updateWithKey (λ _ x → f x)

-- updateWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → Map k a
updateWithKey _ _ Tip               = Tip
updateWithKey f k (Bin sz kx x l r) = case (compare k kx) of
    λ {
      LT → balanceR kx x (updateWithKey f k l) r
    ; GT → balanceL kx x l (updateWithKey f k r)
    ; EQ → case (f kx x) of
        λ {
          (Just x') → Bin sz kx x' l r
        ; Nothing → glue l r
        }
    }

-- updateLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → (Maybe a × Map k a)
updateLookupWithKey _ _ Tip               = (Nothing , Tip)
updateLookupWithKey f k (Bin sz kx x l r) = case (compare k kx) of
    λ {
      LT → let res = updateLookupWithKey f k l
               t' = balanceR kx x (snd res) r
               in (fst res , t')
    ; GT → let res = updateLookupWithKey f k r
               t' = balanceL kx x l (snd res)
               in (fst res , t')
    ; EQ → case (f kx x) of
        λ {
          (Just x') → (Just x' , Bin sz kx x' l r)
        ; Nothing → (Just x , glue l r)
        }
    }


-- alter : {k a : Set} → ⦃ Ord k ⦄ → (Maybe a → Maybe a) → k → Map k a → Map k a
alter f k Tip = case (f Nothing) of
    λ {
      Nothing → Tip
    ; (Just x) → singleton k x
    }
alter f k (Bin sz kx x l r) = case (compare k kx) of
    λ {
      LT → balance kx x (alter f k l) r
    ; GT → balance kx x l (alter f k r)
    ; EQ → case (f (Just x)) of
        λ {
          (Just x') → Bin sz kx x' l r
        ; Nothing → glue l r
        }
    }

-- [TODO] Look into BitQueue
{-------------------
  alterF
-------------------}


-- data AreWeStrict : Set where
--   Lazy : AreWeStrict
--   Strict : AreWeStrict

-- data TraceResult (a : Set) : Set where
--   TraceResultCon : Maybe a → BitQueue → TraceResult a

-- atKeyImpl : {k a : Set} {f : Set} → ⦃ Ord k ⦄ → ⦃ Functor f ⦄ → AreWeStrict → k → (Maybe a → f (Maybe a)) → Map k a → f (Map k a)
-- atKeyImpl strict k f m = case (lookupTrace k m) of
--     λ {
--       (TraceResultCon mv q) → (f <$> mv) (λ fres → case fres of
--           λ {
--             Nothing → case mv of
--                 λ {
--                   Nothing → m
--                 ; (Just old) → deleteAlong old q m
--                 }
--           ; (Just new) → case strict of
--               λ {
--                 Strict → seq new (case mv of
--                     λ {
--                       Nothing → insertAlong q k new m
--                     ; (Just _) → replaceAlong q new m
--                     })
--               ; Lazy → case mv of
--                     λ {
--                       Nothing → insertAlong q k new m
--                     ; (Just _) → replaceAlong q new m
--                     }
--               }
--           })
--     }

-- alterF : {k a : Set} {f : Set} → ⦃ Ord k ⦄ → ⦃ Functor f ⦄ → (Maybe a → f (Maybe a)) → k → Map k a → f (Map k a)
-- alterF f k m = atKeyImpl Lazy k f m

{-------------------
  Indexing
-------------------}

-- findIndex : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → Int
findIndex = go 0
  where
    go : {k a : Set} → ⦃ kOrd : Ord k ⦄ → Int → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → Int
    go _   _ Tip              = error "Map.findIndex: element is not in the map"
    go idx k (Bin _ kx _ l r) = case (compare k kx) of
        λ {
          LT → go idx k l
        ; GT → go (idx + (size l) + 1) k r
        ; EQ → idx + (size l)
        }

-- lookupIndex : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe Int
lookupIndex = go 0
  where
    go : {k a : Set} → ⦃ Ord k ⦄ → Int → k → Map k a → Maybe Int
    go _   _ Tip              = Nothing
    go idx k (Bin _ kx _ l r) = let sizeL = size l in case (compare k kx) of
        λ {
          LT → go idx k l
        ; GT → go (idx + sizeL + 1) k r
        ; EQ → Just (idx + sizeL)
        }

-- elemAt : {k a : Set} → (n : Int) → (map : Map k a) → {Holds ((size map) > 0)} → k × a
elemAt _ Tip = error "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r) = let sizeL = size l in case (compare i sizeL) of
    λ {
      LT → elemAt i l
    ; GT → elemAt (i - sizeL - 1) r
    ; EQ → (kx , x)
    }

-- take : {k a : Set} →  Int → Map k a → Map k a
take _ Tip = Tip
take i m@(Bin _ kx x l r) = let sizeL = size l in if i >= size m then m else (if i <= 0 then Tip else (case (compare i sizeL) of
    λ {
      LT → take i l
    ; GT → link kx x l (take (i - sizeL - 1) r)
    ; EQ → l
    }))

-- drop : {k a : Set} →  Int → Map k a → Map k a
drop _ Tip = Tip
drop i m@(Bin _ kx x l r) = let sizeL = size l in if i >= size m then Tip else (if i <= 0 then m else (case (compare i sizeL) of
    λ {
      LT → link kx x (drop i l) r
    ; GT → drop (i - sizeL - 1) r
    ; EQ → insertMin kx x r
    }))

-- splitAt : {k a : Set} →  Int → Map k a → (Map k a × Map k a)
splitAt _ Tip = Tip , Tip
splitAt i m@(Bin _ kx x l r) = let sizeL = size l in if i >= size m then (m , Tip) else (if i <= 0 then (Tip , m) else (case (compare i sizeL) of
    λ {
      LT → case (splitAt i l) of λ { (ll , lr) → ll , link kx x lr r }
    ; GT → case (splitAt (i - sizeL - 1) r) of λ { (rl , rr) → link kx x l rl , rr }
    ; EQ → l , insertMin kx x r
    }))

-- updateAt : {k a : Set} → (k → a → Maybe a) → Int → (map : Map k a) → {Holds ((size map) > 0)} → Map k a
updateAt f i Tip = error "Map.updateAt: index out of range"
updateAt f i (Bin sz kx x l r) = let sizeL = size l in case (compare i sizeL) of
    λ {
      LT → balanceR kx x (updateAt f i l) r
    ; GT → balanceL kx x l (updateAt f (i - sizeL - 1) r)
    ; EQ → case (f kx x) of
        λ {
          (Just x') → Bin sz kx x' l r
        ; Nothing → glue l r
        }
    }

-- deleteAt : {k a : Set} → Int → (map : Map k a) → {Holds ((size map) > 0)} → Map k a
deleteAt i Tip = error "Map.updateAt: index out of range"
deleteAt i (Bin sz kx x l r) = let sizeL = size l in case (compare i sizeL) of
    λ {
      LT → balanceR kx x (deleteAt i l) r
    ; GT → balanceL kx x l (deleteAt (i - sizeL - 1) r)
    ; EQ → glue l r
    }

{-------------------
  Minimal, Maximal
-------------------}

-- lookupMinSure : {k a : Set} → k → a → Map k a → k × a
lookupMinSure k a Tip = (k , a)
lookupMinSure _ _ (Bin _ kx x l _) = lookupMinSure kx x l

-- lookupMin : {k a : Set} → Map k a → Maybe (k × a)
lookupMin Tip = Nothing
lookupMin (Bin _ kx x l _) = Just $! lookupMinSure kx x l

-- findMin : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → k × a
findMin Tip = error "Map.findMin: empty map has no minimal element"
findMin (Bin _ kx x l _) = lookupMinSure kx x l


-- lookupMaxSure : {k a : Set} → k → a → Map k a → k × a
lookupMaxSure k a Tip = (k , a)
lookupMaxSure _ _ (Bin _ kx x _ r) = lookupMaxSure kx x r

-- lookupMax : {k a : Set} → Map k a → Maybe (k × a)
lookupMax Tip = Nothing
lookupMax (Bin _ kx x _ r) = Just $! lookupMaxSure kx x r

-- findMax : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → k × a
findMax Tip = error "Map.findMax: empty map has no maximal element"
findMax (Bin _ kx x _ r) = lookupMaxSure kx x r


-- deleteMin : {k a : Set} → Map k a → Map k a
deleteMin (Bin _ _  _ Tip r) = r
deleteMin (Bin _ kx x l@(Bin _ _ _ _ _) r) = balanceR kx x (deleteMin l) r
deleteMin Tip = Tip

-- deleteMax : {k a : Set} → Map k a → Map k a
deleteMax (Bin _ _  _ l Tip) = l
deleteMax (Bin _ kx x l r@(Bin _ _ _ _ _)) = balanceL kx x l (deleteMax r)
deleteMax Tip = Tip


-- updateMin : {k a : Set} → (a → Maybe a) → Map k a → Map k a
updateMin f m = updateMinWithKey (λ _ x → f x) m

-- updateMax : {k a : Set} → (a → Maybe a) → Map k a → Map k a
updateMax f m = updateMaxWithKey (λ _ x → f x) m

-- updateMinWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a
updateMinWithKey _ Tip                 = Tip
updateMinWithKey f (Bin sx kx x Tip r) = case (f kx x) of
    λ {
      Nothing → r
    ; (Just x') → Bin sx kx x' Tip r
    }
updateMinWithKey f (Bin _ kx x l@(Bin _ _ _ _ _) r)    = balanceR kx x (updateMinWithKey f l) r


-- updateMaxWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a
updateMaxWithKey _ Tip                 = Tip
updateMaxWithKey f (Bin sx kx x l Tip) = case (f kx x) of
    λ {
      Nothing → l
    ; (Just x') → Bin sx kx x' l Tip
    }
updateMaxWithKey f (Bin _ kx x l r@(Bin _ _ _ _ _))    = balanceL kx x l (updateMaxWithKey f r)

-- minViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)
minViewWithKey Tip = Nothing
minViewWithKey (Bin _ k x l r) = case (minViewSure k x l r) of
    λ {
      (MinViewCon km xm t) → Just ((km , xm) , t)
    }

-- maxViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)
maxViewWithKey Tip = Nothing
maxViewWithKey (Bin _ k x l r) = case (maxViewSure k x l r) of
    λ {
      (MaxViewCon km xm t) → Just ((km , xm) , t)
    }

-- minView : {k a : Set} → Map k a → Maybe (a × Map k a)
minView t = case (minViewWithKey t) of
    λ {
      Nothing → Nothing
    ; (Just ((_ , x) , t')) → Just (x , t')
    }

-- maxView : {k a : Set} → Map k a → Maybe (a × Map k a)
maxView t = case (maxViewWithKey t) of
    λ {
      Nothing → Nothing
    ; (Just ((_ , x) , t')) → Just (x , t')
    }

{-------------------
  Union
-------------------}

-- [TODO] Note : check usage of Foldable.foldl vs Haskell.Prelude.foldl

-- unions : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → f (Map k a) → Map k a
unions ⦃ iFold ⦄ ⦃ iOrd ⦄ ⦃ iEqA ⦄ ⦃ iEqMap ⦄ ts = (Haskell.Prelude.foldl) (union ⦃ iOrd ⦄ ⦃ iEqA ⦄ ⦃ iEqMap ⦄) empty ts

-- unionsWith : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → (a → a → a) → f (Map k a) → Map k a
unionsWith f ts = Haskell.Prelude.foldl (unionWith f) empty ts

-- union : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → Map k a → Map k a → Map k a
union t1 Tip  = t1
union t1 (Bin _ k x Tip Tip) = insertR k x t1
union (Bin _ k x Tip Tip) t2 = insert k x t2
union Tip t2 = t2
union t1@(Bin _ k1 x1 l1 r1) t2 = case (split k1 t2) of
    λ {
      (l2 , r2) → let l1l2 = union l1 l2
                      r1r2 = union r1 r2
                    in link k1 x1 l1l2 r1r2
    }

{-------------------
  Union with a combining function.
-------------------}

-- unionWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → Map k a → Map k a → Map k a
unionWith _f t1 Tip = t1
unionWith f t1 (Bin _ k x Tip Tip) = insertWithR f k x t1
unionWith f (Bin _ k x Tip Tip) t2 = insertWith f k x t2
unionWith _f Tip t2 = t2
unionWith f (Bin _ k1 x1 l1 r1) t2 = case (splitLookup k1 t2) of
    λ {
      (l2 , mb , r2) → let l1l2 = unionWith f l1 l2
                           r1r2 = unionWith f r1 r2
                          in case mb of
          λ {
            Nothing → link k1 x1 l1l2 r1r2
          ; (Just x2) → link k1 (f x1 x2) l1l2 r1r2
          }
    }

-- unionWithKey : {k a : Set} → ⦃ Ord k ⦄ -> (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWithKey _ t1 Tip = t1
unionWithKey f t1 (Bin _ k x Tip Tip) = insertWithKeyR f k x t1
unionWithKey f (Bin _ k x Tip Tip) t2 = insertWithKey f k x t2
unionWithKey _ Tip t2 = t2
unionWithKey f (Bin _ k1 x1 l1 r1) t2 = case (splitLookup k1 t2) of
    λ {
      (l2 , mb , r2) -> let l1l2 = unionWithKey f l1 l2
                            r1r2 = unionWithKey f r1 r2
                          in case mb of
          λ {
            Nothing -> link k1 x1 l1l2 r1r2
          ; (Just x2) -> link k1 (f k1 x1 x2) l1l2 r1r2
          }
    }

{-------------------
  Difference
-------------------}

-- difference : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Map k b -> Map k a
difference Tip _   = Tip
difference t1@(Bin _ _ _ _ _) Tip  = t1
difference t1@(Bin _ _ _ _ _) (Bin _ k _ l2 r2) = case (split k t1) of
    λ {
      (l1 , r1) -> let l1l2 = difference l1 l2
                       r1r2 = difference r1 r2
                    in if (size l1l2 + size r1r2 == size t1) then t1 else (link2 l1l2 r1r2)
    }

-- withoutKeys : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Sett k -> Map k a
withoutKeys Tip _ = Tip
withoutKeys m@(Bin _ _ _ _ _) Sett.Tip = m
withoutKeys m@(Bin _ _ _ _ _) (Sett.Bin _ k ls rs) = case (splitMember k m) of
    λ {
      (lm , b , rm) -> let lm' = withoutKeys lm ls
                           rm' = withoutKeys rm rs
                        in if (not b) then m else (link2 lm' rm')
    }

-- differenceWith : {k a : Set} → ⦃ Ord k ⦄ -> (a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
-- [TODO]

-- differenceWithKey : {k a : Set} → ⦃ Ord k ⦄ -> (k -> a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
-- [TODO]


{-------------------
  Intersection
-------------------}

-- intersection : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Map k b -> Map k a
-- [TODO]

-- restrictKeys : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Sett k -> Map k a
-- [TODO]

-- intersectionWith : {k a : Set} → ⦃ Ord k ⦄ -> (a -> b -> c) -> Map k a -> Map k b -> Map k c
-- [TODO]

-- intersectionWithKey : {k a : Set} → ⦃ Ord k ⦄ -> (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c
-- [TODO]


{-------------------
  glue
-------------------}

-- glue : {k a : Set} → Map k a → Map k a → Map k a
glue Tip r = r
glue l@(Bin _ _ _ _ _) Tip = l
glue l@(Bin sl kl xl ll lr) r@(Bin sr kr xr rl rr) = if (sl > sr)
                                                     then (case (maxViewSure kl xl ll lr) of λ { (MaxViewCon km m l') → balanceR km m l' r})
                                                     else (case (minViewSure kr xr rl rr) of λ { (MinViewCon km m r') → balanceL km m l r'})


-- minViewSure : {k a : Set} → k → a → Map k a → Map k a → MinView k a
minViewSure k x Tip r                 = MinViewCon k x r
minViewSure k x (Bin _ kl xl ll lr) r = case (minViewSure kl xl ll lr) of
    λ {
      (MinViewCon km xm l') → MinViewCon km xm (balanceR k x l' r)
    }

-- maxViewSure : {k a : Set} → k → a → Map k a → Map k a → MaxView k a
maxViewSure k x l Tip                 = MaxViewCon k x l
maxViewSure k x l (Bin _ kr xr rl rr) = case (maxViewSure kr xr rl rr) of
    λ {
      (MaxViewCon km xm r') → MaxViewCon km xm (balanceL k x l r')
    }


-- deleteFindMin : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → ((k × a) × Map k a)
deleteFindMin Tip = (error "Map.deleteFindMin: can not return the minimal element of an empty map" , Tip)
deleteFindMin t@(Bin _ k x l r) = case (minViewSure k x l r) of
    λ {
      (MinViewCon km xm t) → ((km , xm) , t)
    }

-- deleteFindMax : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → ((k × a) × Map k a)
deleteFindMax Tip = (error "Map.deleteFindMax: can not return the maximal element of an empty map" , Tip)
deleteFindMax t@(Bin _ k x l r) = case (maxViewSure k x l r) of
    λ {
      (MaxViewCon km xm t) → ((km , xm) , t)
    }
