module Data.Map.Internal where


open import Haskell.Prelude
    hiding (lookup; map; filter; foldr; foldl; toList; null; splitAt; take; drop)
{-# FOREIGN AGDA2HS
import Prelude hiding (lookup, map, filter, foldr, foldl, null, splitAt, take, drop)
#-}

open import Data.Map.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Datatype
#-}

import Data.Sett.Internal as Sett
{-# FOREIGN AGDA2HS
import qualified Data.Set.Internal as Sett
#-}
open import Data.Sett.Internal using (Sett)
{-# FOREIGN AGDA2HS
import Data.Set.Internal (Set)
#-}

open import Data.Utils.Identity
{-# FOREIGN AGDA2HS
import Data.Functor.Identity (Identity (..))
#-}

open import Data.Utils.Applicative
{-# FOREIGN AGDA2HS
import Control.Applicative (liftA3)
#-}

open import Data.Utils.Bits
{-# FOREIGN AGDA2HS
import Data.Bits (shiftL, shiftR)
#-}


open import Data.Utils.Reasoning
open import Data.Utils.IntegerProofs
open import Data.Map.PreconditionProofs

{---------------------
  Library functions
---------------------}

open import Data.Map.Internal.Query


open import Data.Map.Internal.Operators


open import Data.Map.Internal.Construction


open import Data.Map.Internal.Inserting


open import Data.Map.Internal.Deletion


open import Data.Map.Internal.Indexing


open import Data.Map.Internal.MinMax


open import Data.Map.Internal.Union


open import Data.Map.Internal.Differences


open import Data.Map.Internal.Intersection


-- compose : {a b c : Set} → ⦃ Ord b ⦄ → Map b c → Map a b → Map a c


open import Data.Map.Internal.Merging


open import Data.Map.Internal.Submapping


open import Data.Map.Internal.Filtering


open import Data.Map.Internal.Mapping


open import Data.Map.Internal.Folding


open import Data.Map.Internal.Lists


open import Data.Map.Internal.Splitting


open import Data.Map.Internal.Linking


open import Data.Map.Internal.Balancing


open import Data.Map.Internal.Extras


{--------------------------------------------------------------------------
  Function definitions.
--------------------------------------------------------------------------}

instance
  iSemigroupMap : {k a : Set} → ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ ⦃ _ : Eq (Map k a) ⦄
                  → Semigroup (Map k a)
  iSemigroupMap ._<>_ = union

  iMonoidMap : {k a : Set} → ⦃ _ : Ord k ⦄ ⦃ _ : Eq a ⦄ ⦃ _ : Eq (Map k a) ⦄
               → Monoid (Map k a)
  iMonoidMap .mempty = empty


{-------------------
  Operators
-------------------}

-- _!_ :  {k a : Set} → ⦃ kOrd : Ord k ⦄ → (map : Map k a) → (key : k) → {key ∈ map)} → a
_!_ m k {notEmpty} = find k m {notEmpty}
{-# COMPILE AGDA2HS _!_ #-}

-- _!?_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a -> k -> Maybe a
_!?_ m k = lookup k m
{-# COMPILE AGDA2HS _!?_ #-}

-- _\\_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a -> Map k b -> Map k a
_\\_ m1 m2 = difference m1 m2
{-# COMPILE AGDA2HS _\\_ #-}


{-------------------
  Construction
-------------------}




{-------------------
  Insertion
-------------------}

-- insert : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
insert kx x Tip                 = singleton kx x
insert kx x t@(Bin sz {szPrf} ky y l r) = case (compare kx ky) of
    λ {
      LT → let l' = insert kx x l in if (l' == l) then t else (balanceL ky y l' r)
    ; GT → let r' = insert kx x r in if (r' == r) then t else (balanceR ky y l r')
    ; EQ → if (x == y && kx == ky) then t else (Bin sz {szPrf} kx x l r)
    }
{-# COMPILE AGDA2HS insert #-}

-- insertR : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
insertR kx x Tip                 = singleton kx x
insertR kx x t@(Bin sz ky y l r) = case (compare kx ky) of
    λ {
      LT → let l' = insert kx x l in if (l' == l) then t else (balanceL ky y l' r)
    ; GT → let r' = insert kx x r in if (r' == r) then t else (balanceR ky y l r')
    ; EQ → t
    }
{-# COMPILE AGDA2HS insertR #-}

-- insertWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a
insertWith _ kx x Tip               = singleton kx x
insertWith f kx x (Bin sz {szPrf} ky y l r) = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWith f kx x l) r
    ; GT → balanceR ky y l (insertWith f kx x r)
    ; EQ → Bin sz {szPrf} kx (f x y) l r
    }
{-# COMPILE AGDA2HS insertWith #-}

-- insertWithR : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a
insertWithR _ kx x Tip               = singleton kx x
insertWithR f kx x (Bin sz {szPrf} ky y l r) = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWith f kx x l) r
    ; GT → balanceR ky y l (insertWith f kx x r)
    ; EQ → Bin sz {szPrf} kx (f y x) l r
    }
{-# COMPILE AGDA2HS insertWithR #-}

-- insertWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a
insertWithKey _ kx x Tip                = singleton kx x
insertWithKey f kx x (Bin sz {szPrf} ky y l r)  = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWithKey f kx x l) r
    ; GT → balanceR ky y l (insertWithKey f kx x r)
    ; EQ → Bin sz {szPrf} kx (f kx x y) l r
    }
{-# COMPILE AGDA2HS insertWithKey #-}

-- insertWithKeyR : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a
insertWithKeyR _ kx x Tip                = singleton kx x
insertWithKeyR f kx x (Bin sz {szPrf} ky y l r)  = case (compare kx ky) of
    λ {
      LT → balanceL ky y (insertWithKey f kx x l) r
    ; GT → balanceR ky y l (insertWithKey f kx x r)
    ; EQ → Bin sz {szPrf} kx (f kx y x) l r
    }
{-# COMPILE AGDA2HS insertWithKeyR #-}

-- insertLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → (Maybe a × Map k a)
insertLookupWithKey _ kx x Tip                = (Nothing , singleton kx x)
insertLookupWithKey f kx x (Bin sz {szPrf} ky y l r)  = case (compare kx ky) of
    λ {
      LT → let res = insertLookupWithKey f kx x l
               t' = balanceL ky y (snd res) r
               in (fst res , t')
    ; GT → let res = insertLookupWithKey f kx x r
               t' = balanceR ky y l (snd res)
               in (fst res , t')
    ; EQ → (Just y , Bin sz {szPrf} kx (f kx x y) l r)
    }
{-# COMPILE AGDA2HS insertLookupWithKey #-}


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
{-# COMPILE AGDA2HS delete #-}

-- adjust : {k a : Set} → ⦃ Ord k ⦄ → (a → a) → k → Map k a → Map k a
adjust f = adjustWithKey (λ _ x → f x)
{-# COMPILE AGDA2HS adjust #-}

-- adjustWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a) → k → Map k a → Map k a
adjustWithKey _ _ Tip               = Tip
adjustWithKey f k (Bin sz {szPrf} kx x l r) = case (compare k kx) of
    λ {
      LT → Bin sz {szPrf} kx x (adjustWithKey f k l) r
    ; GT → Bin sz {szPrf} kx x l (adjustWithKey f k r)
    ; EQ → Bin sz {szPrf} kx (f kx x) l r
    }
{-# COMPILE AGDA2HS adjustWithKey #-}

-- update : {k a : Set} → ⦃ Ord k ⦄ → (a → Maybe a) → k → Map k a → Map k a
update f = updateWithKey (λ _ x → f x)
{-# COMPILE AGDA2HS update #-}

-- updateWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → Map k a
updateWithKey _ _ Tip               = Tip
updateWithKey f k (Bin sz {szPrf} kx x l r) = case (compare k kx) of
    λ {
      LT → balanceR kx x (updateWithKey f k l) r
    ; GT → balanceL kx x l (updateWithKey f k r)
    ; EQ → case (f kx x) of
        λ {
          (Just x') → Bin sz {szPrf} kx x' l r
        ; Nothing → glue l r
        }
    }
{-# COMPILE AGDA2HS updateWithKey #-}

-- updateLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → (Maybe a × Map k a)
updateLookupWithKey _ _ Tip               = (Nothing , Tip)
updateLookupWithKey f k (Bin sz {szPrf} kx x l r) = case (compare k kx) of
    λ {
      LT → let res = updateLookupWithKey f k l
               t' = balanceR kx x (snd res) r
               in (fst res , t')
    ; GT → let res = updateLookupWithKey f k r
               t' = balanceL kx x l (snd res)
               in (fst res , t')
    ; EQ → case (f kx x) of
        λ {
          (Just x') → (Just x' , Bin sz {szPrf} kx x' l r)
        ; Nothing → (Just x , glue l r)
        }
    }
{-# COMPILE AGDA2HS updateLookupWithKey #-}

-- alter : {k a : Set} → ⦃ Ord k ⦄ → (Maybe a → Maybe a) → k → Map k a → Map k a
alter f k Tip = case (f Nothing) of
    λ {
      Nothing → Tip
    ; (Just x) → singleton k x
    }
alter f k (Bin sz {szPrf} kx x l r) = case (compare k kx) of
    λ {
      LT → balance kx x (alter f k l) r
    ; GT → balance kx x l (alter f k r)
    ; EQ → case (f (Just x)) of
        λ {
          (Just x') → Bin sz {szPrf} kx x' l r
        ; Nothing → glue l r
        }
    }
{-# COMPILE AGDA2HS alter #-}

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



{-------------------
  Minimal, Maximal
-------------------}

-- lookupMinSure : {k a : Set} → k → a → Map k a → k × a
lookupMinSure k a Tip = (k , a)
lookupMinSure _ _ (Bin _ kx x l _) = lookupMinSure kx x l
{-# COMPILE AGDA2HS lookupMinSure #-}

-- lookupMin : {k a : Set} → Map k a → Maybe (k × a)
lookupMin Tip = Nothing
lookupMin (Bin _ kx x l _) = Just $! lookupMinSure kx x l
{-# COMPILE AGDA2HS lookupMin #-}

-- findMin : {k a : Set} → (map : Map k a) → {IsTrue (not (null map))} → k × a
findMin Tip = error "Map.findMin: empty map has no minimal element"
findMin (Bin _ kx x l _) = lookupMinSure kx x l
{-# COMPILE AGDA2HS findMin #-}

-- lookupMaxSure : {k a : Set} → k → a → Map k a → k × a
lookupMaxSure k a Tip = (k , a)
lookupMaxSure _ _ (Bin _ kx x _ r) = lookupMaxSure kx x r
{-# COMPILE AGDA2HS lookupMaxSure #-}

-- lookupMax : {k a : Set} → Map k a → Maybe (k × a)
lookupMax Tip = Nothing
lookupMax (Bin _ kx x _ r) = Just $! lookupMaxSure kx x r
{-# COMPILE AGDA2HS lookupMax #-}

-- findMax : {k a : Set} → (map : Map k a) → {IsTrue (not (null map))} → k × a
findMax Tip = error "Map.findMax: empty map has no maximal element"
findMax (Bin _ kx x _ r) = lookupMaxSure kx x r
{-# COMPILE AGDA2HS findMax #-}

-- deleteMin : {k a : Set} → Map k a → Map k a
deleteMin (Bin _ _  _ Tip r) = r
deleteMin (Bin _ kx x l@(Bin _ _ _ _ _) r) = balanceR kx x (deleteMin l) r
deleteMin Tip = Tip
{-# COMPILE AGDA2HS deleteMin #-}

-- deleteMax : {k a : Set} → Map k a → Map k a
deleteMax (Bin _ _  _ l Tip) = l
deleteMax (Bin _ kx x l r@(Bin _ _ _ _ _)) = balanceL kx x l (deleteMax r)
deleteMax Tip = Tip
{-# COMPILE AGDA2HS deleteMax #-}

-- updateMin : {k a : Set} → (a → Maybe a) → Map k a → Map k a
updateMin f m = updateMinWithKey (λ _ x → f x) m
{-# COMPILE AGDA2HS updateMin #-}

-- updateMax : {k a : Set} → (a → Maybe a) → Map k a → Map k a
updateMax f m = updateMaxWithKey (λ _ x → f x) m
{-# COMPILE AGDA2HS updateMax #-}

-- updateMinWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a
updateMinWithKey _ Tip                 = Tip
updateMinWithKey f (Bin sx {szPrf} kx x Tip r) = case (f kx x) of
    λ {
      Nothing → r
    ; (Just x') → Bin sx {szPrf} kx x' Tip r
    }
updateMinWithKey f (Bin _ kx x l@(Bin _ _ _ _ _) r)    = balanceR kx x (updateMinWithKey f l) r
{-# COMPILE AGDA2HS updateMinWithKey #-}

-- updateMaxWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a
updateMaxWithKey _ Tip                 = Tip
updateMaxWithKey f (Bin sx {szPrf} kx x l Tip) = case (f kx x) of
    λ {
      Nothing → l
    ; (Just x') → Bin sx {szPrf} kx x' l Tip
    }
updateMaxWithKey f (Bin _ kx x l r@(Bin _ _ _ _ _))    = balanceL kx x l (updateMaxWithKey f r)
{-# COMPILE AGDA2HS updateMaxWithKey #-}

-- minViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)
minViewWithKey Tip = Nothing
minViewWithKey (Bin _ k x l r) = case (minViewSure k x l r) of
    λ {
      (MinViewCon km xm t) → Just ((km , xm) , t)
    }
{-# COMPILE AGDA2HS minViewWithKey #-}

-- maxViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)
maxViewWithKey Tip = Nothing
maxViewWithKey (Bin _ k x l r) = case (maxViewSure k x l r) of
    λ {
      (MaxViewCon km xm t) → Just ((km , xm) , t)
    }
{-# COMPILE AGDA2HS maxViewWithKey #-}

-- minView : {k a : Set} → Map k a → Maybe (a × Map k a)
minView t = case (minViewWithKey t) of
    λ {
      Nothing → Nothing
    ; (Just ((_ , x) , t')) → Just (x , t')
    }
{-# COMPILE AGDA2HS minView #-}

-- maxView : {k a : Set} → Map k a → Maybe (a × Map k a)
maxView t = case (maxViewWithKey t) of
    λ {
      Nothing → Nothing
    ; (Just ((_ , x) , t')) → Just (x , t')
    }
{-# COMPILE AGDA2HS maxView #-}

{-------------------
  Union
-------------------}

-- [TODO] Note : check usage of Foldable.foldl vs Haskell.Prelude.foldl

-- unions : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → f (Map k a) → Map k a
unions ⦃ iFold ⦄ ⦃ iOrd ⦄ ⦃ iEqA ⦄ ⦃ iEqMap ⦄ ts = Haskell.Prelude.foldl (union ⦃ iOrd ⦄ ⦃ iEqA ⦄ ⦃ iEqMap ⦄) empty ts
{-# COMPILE AGDA2HS unions #-}

-- unionsWith : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → (a → a → a) → f (Map k a) → Map k a
unionsWith f ts = Haskell.Prelude.foldl (unionWith f) empty ts
{-# COMPILE AGDA2HS unionsWith #-}

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
{-# COMPILE AGDA2HS union #-}

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
{-# COMPILE AGDA2HS unionWith #-}

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
{-# COMPILE AGDA2HS unionWithKey #-}

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
{-# COMPILE AGDA2HS difference #-}

-- withoutKeys : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Sett k -> Map k a
withoutKeys Tip _ = Tip
withoutKeys m@(Bin _ _ _ _ _) Sett.Tip = m
withoutKeys m@(Bin _ _ _ _ _) (Sett.Bin _ k ls rs) = case (splitMember k m) of
    λ {
      (lm , b , rm) -> let lm' = withoutKeys lm ls
                           rm' = withoutKeys rm rs
                        in if (not b) then m else (link2 lm' rm')
    }
{-# COMPILE AGDA2HS withoutKeys #-}

-- differenceWith : {k a : Set} → ⦃ Ord k ⦄ -> (a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
-- [TODO]

-- differenceWithKey : {k a : Set} → ⦃ Ord k ⦄ -> (k -> a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
-- [TODO]


{-------------------
  Intersection
-------------------}

-- intersection : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Map k b -> Map k a
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Bin _ k x l1 r1) t2 = case (splitMember k t2) of
    λ {
      (l2 , mb , r2) → let l1l2 = intersection l1 l2
                           r1r2 = intersection r1 r2
                        in if mb
                           then (link k x l1l2 r1r2)
                           else (link2 l1l2 r1r2)
    }
{-# COMPILE AGDA2HS intersection #-}

-- restrictKeys : {k a : Set} → ⦃ Ord k ⦄ -> Map k a -> Sett k -> Map k a
restrictKeys Tip _ = Tip
restrictKeys _ Sett.Tip = Tip
restrictKeys m@(Bin _ k x l1 r1) s = case (Sett.splitMember k s) of
    λ {
      (l2 , b , r2) → let l1l2 = restrictKeys l1 l2
                          r1r2 = restrictKeys r1 r2
                        in if b
                           then (link k x l1l2 r1r2)
                           else (link2 l1l2 r1r2)
    }
{-# COMPILE AGDA2HS restrictKeys #-}

-- intersectionWith : {k a : Set} → ⦃ Ord k ⦄ -> (a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWith _ Tip _ = Tip
intersectionWith _ _ Tip = Tip
intersectionWith f (Bin _ k x1 l1 r1) t2 = case (splitLookup k t2) of
    λ {
      (l2 , mb , r2) → let l1l2 = intersectionWith f l1 l2
                           r1r2 = intersectionWith f r1 r2
                        in case mb of
                            λ {
                              (Just x2) → link k (f x1 x2) l1l2 r1r2
                            ; Nothing → link2 l1l2 r1r2
                            }
    }
{-# COMPILE AGDA2HS intersectionWith #-}

-- intersectionWithKey : {k a : Set} → ⦃ Ord k ⦄ -> (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWithKey _ Tip _ = Tip
intersectionWithKey _ _ Tip = Tip
intersectionWithKey f (Bin _ k x1 l1 r1) t2 = case (splitLookup k t2) of
    λ {
      (l2 , mb , r2) → let l1l2 = intersectionWithKey f l1 l2
                           r1r2 = intersectionWithKey f r1 r2
                        in case mb of
                            λ {
                              (Just x2) → link k (f k x1 x2) l1l2 r1r2
                            ; Nothing → link2 l1l2 r1r2
                            }
    }
{-# COMPILE AGDA2HS intersectionWithKey #-}


{-------------------
  Disjoint
-------------------}

-- disjoint : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Bool
disjoint Tip _ = true
disjoint _ Tip = true
disjoint (Bin sz k _ l r) t =
    if (sz == 1)
    then (notMember k t)
    else case (splitMember k t) of
        λ {
          (lt , found , gt) → not found && disjoint l lt && disjoint r gt
        }
{-# COMPILE AGDA2HS disjoint #-}


{-------------------
  Compose
-------------------}

-- compose : ⦃ Ord b ⦄ → Map b c → Map a b → Map a c

{-------------------
  mergeWithKey
-------------------}

-- mergeWithKey : {k a b c : Set} → ⦃ Ord k ⦄ → ⦃ Ord b ⦄ → (k → a → b → Maybe c)
--              → (Map k a → Map k c) → (Map k b → Map k c)
--              → Map k a → Map k b → Map k c

mergeWithKey {k} {a} {b} {c} f g1 g2 = go
  where
    go : Map k a → Map k b → Map k c
    go Tip t2 = g2 t2
    go t1@(Bin _ _ _ _ _) Tip = g1 t1
    go (Bin _ kx x l1 r1) t2 = case (splitLookup kx t2) of
        λ {
          (l2 , found , r2) → let l' = go l1 l2
                                  r' = (go r1 r2)
              in case found of
              λ {
                Nothing -> case (g1 (singleton kx x)) of
                    λ {
                      Tip -> link2 l' r'
                    ; (Bin _ _ x' Tip Tip) -> link kx x' l' r'
                    ; _ -> Tip
                    }
              ; (Just x2) -> case (f kx x x2) of
                  λ {
                    Nothing -> link2 l' r'
                  ; (Just x') -> link kx x' l' r'
                  }
              }
        }
{-# COMPILE AGDA2HS mergeWithKey #-}


{-------------------
  Submap
-------------------}

-- isSubmapOf : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → Map k a -> Map k a -> Bool
isSubmapOf m1 m2 = isSubmapOfBy (_==_) m1 m2
{-# COMPILE AGDA2HS isSubmapOf #-}

-- isSubmapOfBy : {k a b : Set} → ⦃ Ord k ⦄ → (a -> b -> Bool) -> Map k a -> Map k b -> Bool
isSubmapOfBy ⦃ kOrd ⦄ f t1 t2 = (size t1 <= size t2) && (submap' ⦃ kOrd ⦄ f t1 t2)
{-# COMPILE AGDA2HS isSubmapOfBy #-}

-- submap' : {a b c : Set} → ⦃ Ord a ⦄ → (b -> c -> Bool) -> Map a b -> Map a c -> Bool
submap' _ Tip _ = true
submap' _ _ Tip = false
submap' f (Bin sz kx x l r) t =
    if (sz == 1)
    then (case (lookup kx t) of
        λ {
          (Just y) -> f x y
        ; Nothing -> false
        })
    else (case (splitLookup kx t) of
        λ {
              (lt , found , gt) -> case found of
                  λ {
                    Nothing -> false
                  ; (Just y) -> (f x y)
                                && (size l <= size lt) && (size r <= size gt)
                                && (submap' f l lt) && (submap' f r gt)
                  }
        })
{-# COMPILE AGDA2HS submap' #-}

-- isProperSubmapOf : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → Map k a -> Map k a -> Bool
isProperSubmapOf m1 m2 = isProperSubmapOfBy (_==_) m1 m2
{-# COMPILE AGDA2HS isProperSubmapOf #-}

-- isProperSubmapOfBy : {k a : Set} → ⦃ Ord k ⦄ → (a -> b -> Bool) -> Map k a -> Map k b -> Bool
isProperSubmapOfBy f t1 t2 = (size t1 < size t2) && (submap' f t1 t2)
{-# COMPILE AGDA2HS isProperSubmapOfBy #-}


{-------------------
  Filter and partition
-------------------}

-- filter : {k a : Set} → (a -> Bool) -> Map k a -> Map k a
filter p m = filterWithKey (λ _ x -> p x) m

-- filterWithKey : {k a : Set} → (k -> a -> Bool) -> Map k a -> Map k a
filterWithKey _ Tip = Tip
filterWithKey p t@(Bin _ kx x l r) =
    let pl = filterWithKey p l
        pr = filterWithKey p r
    in if (p kx x)
    then (link kx x pl pr)
    else (link2 pl pr)
{-# COMPILE AGDA2HS filterWithKey #-}

-- filterWithKeyA : {k a : Set} → {f : Set → Set} → ⦃ Applicative f ⦄ → (k -> a -> f Bool) -> Map k a -> f (Map k a)
filterWithKeyA _ Tip = pure Tip
filterWithKeyA {k} {a} ⦃ fApp ⦄ p (Bin _ kx x l r) =  pure Tip -- liftA3 combine (p kx x) (filterWithKeyA p l) (filterWithKeyA p r)
  where
    combine : Bool → Map k a → Map k a → Map k a
    combine true pl pr = link kx x pl pr
    combine false pl pr = link2 pl pr
{-# COMPILE AGDA2HS filterWithKeyA #-}

-- takeWhileAntitone : {k a : Set} → (k -> Bool) -> Map k a -> Map k a
takeWhileAntitone _ Tip = Tip
takeWhileAntitone p (Bin _ kx x l r) =
    if (p kx)
    then (link kx x l (takeWhileAntitone p r))
    else (takeWhileAntitone p l)
{-# COMPILE AGDA2HS takeWhileAntitone #-}

-- dropWhileAntitone : {k a : Set} → (k -> Bool) -> Map k a -> Map k a
dropWhileAntitone _ Tip = Tip
dropWhileAntitone p (Bin _ kx x l r) =
    if (p kx)
    then (dropWhileAntitone p r)
    else (link kx x (dropWhileAntitone p l) r)
{-# COMPILE AGDA2HS dropWhileAntitone #-}

-- spanAntitone : {k a : Set} → (k -> Bool) -> Map k a -> (Map k a) × (Map k a)
spanAntitone _ Tip = Tip , Tip
spanAntitone p (Bin _ kx x l r) =
    if (p kx)
    then (case (spanAntitone p r) of λ { (u , v) → link kx x l u , v })
    else (case (spanAntitone p l) of λ { (u , v) → u , link kx x v r })
{-# COMPILE AGDA2HS spanAntitone #-}

-- partition : {k a : Set} → (a -> Bool) -> Map k a -> (Map k a) × (Map k a)
partition p m = partitionWithKey (λ _ x -> p x) m
{-# COMPILE AGDA2HS partition #-}

-- partitionWithKey : {k a : Set} → (k -> a -> Bool) -> Map k a -> (Map k a) × (Map k a)
partitionWithKey _ Tip = (Tip , Tip)
partitionWithKey p t@(Bin _ kx x l r) = let p1 = partitionWithKey p l
                                            l1 = fst p1
                                            l2 = snd p1
                                            p2 = partitionWithKey p r
                                            r1 = fst p2
                                            r2 = snd p2
    in if (p kx x)
    then (link kx x l1 r1 , link2 l2 r2)
    else (link2 l1 r1 , link kx x l2 r2)
{-# COMPILE AGDA2HS partitionWithKey #-}

-- mapMaybe : {k a : Set} → (a -> Maybe b) -> Map k a -> Map k b
mapMaybe f = mapMaybeWithKey (λ _ x -> f x)
{-# COMPILE AGDA2HS mapMaybe #-}

-- mapMaybeWithKey : {k a : Set} → (k -> a -> Maybe b) -> Map k a -> Map k b
mapMaybeWithKey _ Tip = Tip
mapMaybeWithKey f (Bin _ kx x l r) = case (f kx x) of
    λ {
      (Just y)  -> link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
    ; Nothing -> link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)
    }
{-# COMPILE AGDA2HS mapMaybeWithKey #-}

-- traverseMaybeWithKey : {k a b : Set} → {f : Set → Set} → ⦃ Applicative f ⦄ → (k -> a -> f (Maybe b)) -> Map k a -> f (Map k b)
traverseMaybeWithKey _ Tip = pure Tip
traverseMaybeWithKey p (Bin _ kx x Tip Tip) = maybe Tip (λ x' -> Bin 1 kx x' Tip Tip) <$> p kx x
traverseMaybeWithKey {k} {a} {b} p (Bin _ kx x l r) = liftA3 combine (traverseMaybeWithKey p l) (p kx x) (traverseMaybeWithKey p r)
  where
    combine : Map k b → Maybe b → Map k b → Map k b
    combine l' mx r' = case mx of
        λ {
          Nothing -> link2 l' r'
        ; (Just x') -> link kx x' l' r'
        }
{-# COMPILE AGDA2HS traverseMaybeWithKey #-}

-- mapEither : {k a b c : Set} → (a -> Either b c) -> Map k a -> (Map k b) × (Map k c)
mapEither f m = mapEitherWithKey (λ _ x -> f x) m
{-# COMPILE AGDA2HS mapEither #-}

-- mapEitherWithKey : {k a b c : Set} → (k -> a -> Either b c) -> Map k a -> (Map k b) × (Map k c)
mapEitherWithKey _ Tip = (Tip , Tip)
mapEitherWithKey p (Bin _ kx x l r) = let p1 = mapEitherWithKey p l
                                          l1 = fst p1
                                          l2 = snd p1
                                          p2 = mapEitherWithKey p r
                                          r1 = fst p2
                                          r2 = snd p2
  in case (p kx x) of
    λ {
      (Left y)  -> link kx y l1 r1 , link2 l2 r2
    ; (Right z) -> link2 l1 r1 , link kx z l2 r2
    }
{-# COMPILE AGDA2HS mapEitherWithKey #-}


{-------------------
  Mapping
-------------------}

-- map : {k a : Set} → (a -> b) -> Map k a -> Map k b
map f Tip = Tip
map f (Bin sx {szPrf} kx x l r) = Bin sx {szPrf} kx (f x) (map f l) (map f r)
{-# COMPILE AGDA2HS map #-}

-- mapWithKey : {k a : Set} → (k -> a -> b) -> Map k a -> Map k b
mapWithKey _ Tip = Tip
mapWithKey f (Bin sx {szPrf} kx x l r) = Bin sx {szPrf} kx (f kx x) (mapWithKey f l) (mapWithKey f r)
{-# COMPILE AGDA2HS mapWithKey #-}

-- traverseWithKey : {k a : Set} → {t : Set → Set} → ⦃ Applicative t ⦄ → (k -> a -> t b) -> Map k a -> t (Map k b)
traverseWithKey f Tip = pure Tip
traverseWithKey f (Bin s {szPrf} k v l r) =
    if s == 1
    then ((λ v' -> Bin 1 k v' Tip Tip) <$> f k v)
    else (liftA3 (flip (Bin s {szPrf} k)) (traverseWithKey f l) (f k v) (traverseWithKey f r))
{-# COMPILE AGDA2HS traverseWithKey #-}

-- mapAccum : {k a b c : Set} → (a -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
mapAccum f a m = mapAccumWithKey (λ a' _ x' -> f a' x') a m
{-# COMPILE AGDA2HS mapAccum #-}

-- mapAccumWithKey : {k a b c : Set} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
mapAccumWithKey f a t = mapAccumL f a t
{-# COMPILE AGDA2HS mapAccumWithKey #-}

-- mapAccumL : {k a b c : Set} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
mapAccumL _ a Tip               = (a , Tip)
mapAccumL f a (Bin sz {szPrf} kx x l r) = (a3 , Bin sz {szPrf} kx x' l' r')
  where
    p1 = mapAccumL f a l
    a1 = fst p1
    l' = snd p1
    p2 = f a1 kx x
    a2 = fst p2
    x' = snd p2
    p3 = mapAccumL f a2 r
    a3 = fst p3
    r' = snd p3
{-# COMPILE AGDA2HS mapAccumL #-}

-- mapAccumRWithKey : {k a b c : Set} → (a -> k -> b -> (a × c)) -> a -> Map k b -> (a × Map k c)
mapAccumRWithKey _ a Tip = (a , Tip)
mapAccumRWithKey f a (Bin sx {szPrf} kx x l r) = (a3 , Bin sx {szPrf} kx x' l' r')
  where
    p1 = mapAccumRWithKey f a r
    a1 = fst p1
    r' = snd p1
    p2 = f a1 kx x
    a2 = fst p2
    x' = snd p2
    p3 = mapAccumRWithKey f a2 l
    a3 = fst p3
    l' = snd p3
{-# COMPILE AGDA2HS mapAccumRWithKey #-}

-- mapKeys : {k1 k2 a : Set} → ⦃ Ord k2 ⦄ -> (k1 -> k2) -> Map k1 a -> Map k2 a
mapKeys f t = fromList $ foldrWithKey (λ k x xs -> (f k , x) ∷ xs) [] t
{-# COMPILE AGDA2HS mapKeys #-}

-- mapKeysWith : {k1 k2 a : Set} → ⦃ Ord k2 ⦄ -> (a -> a -> a) -> (k1 -> k2) -> Map k1 a -> Map k2 a
mapKeysWith c f t = (fromListWith c) $ foldrWithKey (\k x xs -> (f k , x) ∷ xs) [] t
{-# COMPILE AGDA2HS mapKeysWith #-}

-- mapKeysMonotonic : {k1 k2 a : Set} → (k1 -> k2) -> Map k1 a -> Map k2 a
mapKeysMonotonic _ Tip = Tip
mapKeysMonotonic f (Bin sz {szPrf} k x l r) =
    Bin sz {szPrf} (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)
{-# COMPILE AGDA2HS mapKeysMonotonic #-}


{-------------------
  Folds
-------------------}

-- foldr : {k a b : Set} → (a -> b -> b) -> b -> Map k a -> b
foldr {k} {a} {b} f z = go z
  where
    go : b → Map k a → b
    go z' Tip             = z'
    go z' (Bin _ _ x l r) = go (f x (go z' r)) l
{-# COMPILE AGDA2HS foldr #-}

-- foldr' : {k a b : Set} → (a -> b -> b) -> b -> Map k a -> b
foldr' {k} {a} {b} f z = go z
  where
    go : b → Map k a → b
    go z' Tip             = seq z' z'
    go z' (Bin _ _ x l r) = go (f x (go z' r)) l
{-# COMPILE AGDA2HS foldr' #-}

-- foldl : {k a b : Set} → (a -> b -> a) -> a -> Map k b -> a
foldl {k} {a} {b} f z = go z
  where
    go : a → Map k b → a
    go z' Tip             = z'
    go z' (Bin _ _ x l r) = go (f (go z' l) x) r
{-# COMPILE AGDA2HS foldl #-}

-- foldl' : {k a b : Set} → (a -> b -> a) -> a -> Map k b -> a
foldl' {k} {a} {b} f z = go z
  where
    go : a → Map k b → a
    go z' Tip             = seq z' z'
    go z' (Bin _ _ x l r) = go (f (go z' l) x) r
{-# COMPILE AGDA2HS foldl' #-}

-- foldrWithKey : {k a b : Set} → (k -> a -> b -> b) -> b -> Map k a -> b
foldrWithKey {k} {a} {b} f z = go z
  where
    go : b → Map k a → b
    go z' Tip             = z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
{-# COMPILE AGDA2HS foldrWithKey #-}

-- foldrWithKey' : {k a b : Set} → (k -> a -> b -> b) -> b -> Map k a -> b
foldrWithKey' {k} {a} {b} f z = go z
  where
    go : b → Map k a → b
    go z' Tip             = seq z' z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
{-# COMPILE AGDA2HS foldrWithKey' #-}

-- foldlWithKey : {k a b : Set} → (a -> k -> b -> a) -> a -> Map k b -> a
foldlWithKey {k} {a} {b} f z = go z
  where
    go : a → Map k b → a
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
{-# COMPILE AGDA2HS foldlWithKey #-}

-- foldlWithKey' : {k a b : Set} → (a -> k -> b -> a) -> a -> Map k b -> a
foldlWithKey' {k} {a} {b} f z = go z
  where
    go : a → Map k b → a
    go z' Tip              = seq z' z'
    go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
{-# COMPILE AGDA2HS foldlWithKey' #-}

-- foldMapWithKey : {k a m : Set} → ⦃ Monoid m ⦄ -> (k -> a -> m) -> Map k a -> m
foldMapWithKey {k} {a} {m} f = go
  where
    go : Map k a -> m
    go Tip             = mempty
    go (Bin sz k v l r) =
      if sz == 1
      then (f k v)
      else (mappend (go l) (mappend (f k v) (go r)))
{-# COMPILE AGDA2HS foldMapWithKey #-}


{-------------------
  List variations
-------------------}

-- elems : {k a : Set} → Map k a -> List a
elems = foldr (_∷_) []
{-# COMPILE AGDA2HS elems #-}

-- keys  : {k a : Set} → Map k a -> List k
keys = foldrWithKey (λ k _ ks -> k ∷ ks) []
{-# COMPILE AGDA2HS keys #-}

-- assocs : {k a : Set} → Map k a -> List (k × a)
assocs m = toAscList m
{-# COMPILE AGDA2HS assocs #-}

-- keysSet : {k a : Set} → Map k a -> Sett.Sett k
keysSet Tip = Sett.Tip
keysSet (Bin sz {szPrf} kx _ l r) = Sett.Bin sz {szPrf} kx (keysSet l) (keysSet r)
{-# COMPILE AGDA2HS keysSet #-}

-- fromSet : {k a : Set} → (k -> a) -> Sett.Sett k -> Map k a
fromSet _ Sett.Tip = Tip
fromSet f (Sett.Bin sz {szPrf} x l r) = Bin sz {szPrf} x (f x) (fromSet f l) (fromSet f r)
{-# COMPILE AGDA2HS fromSet #-}


{-------------------
  Lists
-------------------}


{-# TERMINATING #-}
-- fromList : {k a : Set} → ⦃ Ord k ⦄ → List (k × a) -> Map k a
fromList [] = Tip
fromList ((kx , x) ∷ []) = Bin 1 kx x Tip Tip
fromList {k} {a} ((kx0 , x0) ∷ xs0) =
    if (not_ordered kx0 xs0)
    then (fromList' (Bin 1 kx0 x0 Tip Tip) xs0)
    else (go 1 (Bin 1 kx0 x0 Tip Tip) xs0)
  where
    not_ordered : k → List (k × a) → Bool
    not_ordered _ [] = false
    not_ordered kx ((ky , _) ∷ _) = kx >= ky

    fromList' : Map k a → List (k × a) → Map k a
    fromList' t0 xs = Haskell.Prelude.foldl ins t0 xs
      where
        ins : Map k a → (k × a) → Map k a
        ins t (k , x) = insert k x t

    create : Int → List (k × a) → (Map k a) × (List (k × a)) × (List (k × a))
    create _ [] = (Tip , [] , [])
    create s xs@((kx , x) ∷ xss) =
      if (s == 1)
      then (if (not_ordered kx xss)
            then (Bin 1 kx x Tip Tip , [] , xss)
            else (Bin 1 kx x Tip Tip , xss , []))
      else (case (create (shiftR s 1) xs) of
              λ {
                res@(_ , [] , _) -> res
              ; (l , ((ky , y) ∷ []) , zs) -> (insertMax ky y l , [] , zs)
              ; (l , ys@((ky , y) ∷ yss) , _) →
                if (not_ordered ky yss)
                then (l , [] , ys)
                else (case create (shiftR s 1) yss of
                        λ { (r , zs , ws) -> (link ky y l r , zs , ws) })
              })

    go : Int → Map k a → List (k × a) → Map k a
    go _ t [] = t
    go _ t ((kx , x) ∷ []) = insertMax kx x t
    go s l xs@((kx , x) ∷ xss) =
        if (not_ordered kx xss)
        then (fromList' l xs)
        else (case create s xss of
                λ {
                  (r , ys , []) -> go (shiftL s 1) (link kx x l r) ys
                ; (r , _ ,  ys) -> fromList' (link kx x l r) ys
                })


-- fromListWith : {k a : Set} → ⦃ Ord k ⦄ → (a -> a -> a) -> List (k × a) -> Map k a
fromListWith f xs
  = fromListWithKey (λ _ x y -> f x y) xs

-- fromListWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k -> a -> a -> a) -> List (k × a) -> Map k a
fromListWithKey {k} {a} f xs
  = Haskell.Prelude.foldl ins empty xs
  where
    ins : Map k a → (k × a) → Map k a
    ins t (k , x) = insertWithKey f k x t

-- toList : {k a : Set} → Map k a -> List (k × a)
toList = toAscList

-- toAscList : {k a : Set} → Map k a -> List (k × a)
toAscList = foldrWithKey (λ k x xs -> (k , x) ∷ xs) []

-- toDescList : {k a : Set} → Map k a -> List (k × a)
toDescList = foldlWithKey (λ xs k x -> (k , x) ∷ xs) []

-- foldrFB : {k a : Set} → (k -> a -> b -> b) -> b -> Map k a -> b
foldrFB = foldrWithKey

-- foldlFB : {k a : Set} → (a -> k -> b -> a) -> a -> Map k b -> a
foldlFB = foldlWithKey

combineEq' : {k a : Set} → ⦃ Eq k ⦄ → (k -> a -> a -> a) → (k × a) → List (k × a) → List (k × a)
combineEq' _ z [] = z ∷ []
combineEq' f z@(kz , zz) (x@(kx , xx) ∷ xs') =
  if (kx == kz)
  then (let yy = (f kx xx zz) in combineEq' f (kx , yy) xs')
  else (z ∷ combineEq' f x xs')

combineEq : {k a : Set} → ⦃ Eq k ⦄ → (k -> a -> a -> a) → List (k × a) → List (k × a)
combineEq f xs' = case xs' of
  λ {
    []        -> []
  ; (x ∷ [])  -> x ∷ []
  ; (x ∷ xx)  -> combineEq' f x xx
  }

-- fromAscList : {k a : Set} → ⦃ Eq k ⦄ → List (k × a) -> Map k a
fromAscList {k} {a} xs = fromDistinctAscList (combineEq (λ _ x _ → x) xs)

-- fromDescList : {k a : Set} → ⦃ Eq k ⦄ → List (k × a) -> Map k a
fromDescList {k} {a} xs = fromDistinctDescList (combineEq (λ _ x _ → x) xs)

-- fromAscListWith : {k a : Set} → ⦃ Eq k ⦄ → (a -> a -> a) -> List (k × a) -> Map k a
fromAscListWith f xs
  = fromAscListWithKey (λ _ x y -> f x y) xs

-- fromDescListWith : {k a : Set} → ⦃ Eq k ⦄ → (a -> a -> a) -> List (k × a) -> Map k a
fromDescListWith f xs
  = fromDescListWithKey (λ _ x y -> f x y) xs

-- fromAscListWithKey : {k a : Set} → ⦃ Eq k ⦄ → (k -> a -> a -> a) -> List (k × a) -> Map k a
fromAscListWithKey f xs
  = fromDistinctAscList (combineEq f xs)

-- fromDescListWithKey : {k a : Set} → ⦃ Eq k ⦄ → (k -> a -> a -> a) -> List (k × a) -> Map k a
fromDescListWithKey f xs
  = fromDistinctDescList (combineEq f xs)

-- fromDistinctAscList : {k a : Set} → List (k × a) -> Map k a
fromDistinctAscList [] = Tip
fromDistinctAscList {k} {a} ((kx0 , x0) ∷ xs0) = go 1 (Bin 1 kx0 x0 Tip Tip) xs0
  where
    create : Int → List (k × a) → (Map k a) × List (k × a)
    create _ [] = (Tip , [])
    create s xs@(x' ∷ xs') =
      if (s == 1)
      then (case x' of λ { (kx , x) -> (Bin 1 kx x Tip Tip , xs') })
      else (case create (shiftR s 1) xs of
              λ {
                res@(_ , []) -> res
              ; (l , (ky , y) ∷ ys) -> case create (shiftR s 1) ys of
                  λ { (r , zs) -> (link ky y l r , zs) }
              })

    go : Int → Map k a → List (k × a) → Map k a
    go _ t [] = t
    go s l ((kx , x) ∷ xs) = case create s xs of
      λ { (r , ys) -> let t' = link kx x l r
                    in go (shiftL s 1) t' ys }


-- fromDistinctDescList : {k a : Set} → List (k × a) -> Map k a
fromDistinctDescList [] = Tip
fromDistinctDescList {k} {a} ((kx0 , x0) ∷ xs0) = go 1 (Bin 1 kx0 x0 Tip Tip) xs0
  where
    create : Int → List (k × a) → (Map k a) × List (k × a)
    create _ [] = (Tip , [])
    create s xs@(x' ∷ xs') =
      if (s == 1)
      then (case x' of λ { (kx , x) -> (Bin 1 kx x Tip Tip , xs') })
      else (case create (shiftR s 1) xs of
              λ {
                res@(_ , []) -> res
              ; (r , (ky , y) ∷ ys) -> case create (shiftR s 1) ys of
                  λ { (l , zs) -> (link ky y l r , zs) }
              })

    go : Int → Map k a → List (k × a) → Map k a
    go _ t [] = t
    go s r ((kx , x) ∷ xs) = case create s xs of
      λ { (l , ys) -> let t' = link kx x l r
                    in go (shiftL s 1) t' ys }



{-------------------
  Split
-------------------}

-- split : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Map k a)
split k Tip = Tip , Tip
split k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT -> case (split k l) of (λ { (lt , gt) → lt , link kx x gt r})
    ; GT -> case (split k r) of (λ { (lt , gt) → link kx x l lt , gt})
    ; EQ -> (l , r)
    }
{-# COMPILE AGDA2HS split #-}

-- splitLookup : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Maybe a × Map k a)
splitLookup k Tip = Tip , Nothing , Tip
splitLookup k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT -> case (splitLookup k l) of (λ { (lt , z , gt) → lt , z , link kx x gt r })
    ; GT -> case (splitLookup k r) of (λ { (lt , z , gt) → link kx x l lt , z , gt })
    ; EQ -> l , (Just x) , r
    }
{-# COMPILE AGDA2HS splitLookup #-}

-- splitMember : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Bool × Map k a)
splitMember k Tip = Tip , false , Tip
splitMember k (Bin _ kx x l r) = case (compare k kx) of
    λ {
      LT -> case (splitMember k l) of (λ { (lt , z , gt) → lt , z , link kx x gt r })
    ; GT -> case (splitMember k r) of (λ { (lt , z , gt) → link kx x l lt , z , gt })
    ; EQ -> l , true , r
    }
{-# COMPILE AGDA2HS splitMember #-}


{-------------------
  link
-------------------}

-- link : {k a : Set} → k → a → Map k a → Map k a → Map k a
link kx x Tip r  = insertMin kx x r
link kx x l Tip  = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz) =
  if (delta * sizeL < sizeR)
  then (balanceL kz z (link kx x l lz) rz)
  else (if (delta * sizeR < sizeL)
        then (balanceR ky y ly (link kx x ry r))
        else (bin kx x l r))
{-# COMPILE AGDA2HS link #-}

-- insertMax : {k a : Set} → k → a → Map k a → Map k a
insertMax kx x Tip = singleton kx x
insertMax kx x (Bin _ ky y l r) = balanceR ky y l (insertMax kx x r)
{-# COMPILE AGDA2HS insertMax #-}

-- insertMin : {k a : Set} → k → a → Map k a → Map k a
insertMin kx x Tip = singleton kx x
insertMin kx x (Bin _ ky y l r) = balanceL ky y (insertMin kx x l) r
{-# COMPILE AGDA2HS insertMin #-}


{-------------------
  link2
-------------------}

-- link2 : {k a : Set} → Map k a → Map k a → Map k a
link2 Tip r   = r
link2 l Tip   = l
link2 l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry) =
  if (delta * sizeL < sizeR)
  then (balanceL ky y (link2 l ly) ry)
  else (if (delta * sizeR < sizeL)
        then (balanceR kx x lx (link2 rx r))
        else (glue l r))
{-# COMPILE AGDA2HS link2 #-}


{-------------------
  glue
-------------------}

-- glue : {k a : Set} → Map k a → Map k a → Map k a
glue Tip r = r
glue l@(Bin _ _ _ _ _) Tip = l
glue l@(Bin sl kl xl ll lr) r@(Bin sr kr xr rl rr) = if (sl > sr)
                                                     then (case (maxViewSure kl xl ll lr) of λ { (MaxViewCon km m l') → balanceR km m l' r})
                                                     else (case (minViewSure kr xr rl rr) of λ { (MinViewCon km m r') → balanceL km m l r'})
{-# COMPILE AGDA2HS glue #-}

-- minViewSure : {k a : Set} → k → a → Map k a → Map k a → MinView k a
minViewSure k x Tip r                 = MinViewCon k x r
minViewSure k x (Bin _ kl xl ll lr) r = case (minViewSure kl xl ll lr) of
    λ {
      (MinViewCon km xm l') → MinViewCon km xm (balanceR k x l' r)
    }
{-# COMPILE AGDA2HS minViewSure #-}

-- maxViewSure : {k a : Set} → k → a → Map k a → Map k a → MaxView k a
maxViewSure k x l Tip                 = MaxViewCon k x l
maxViewSure k x l (Bin _ kr xr rl rr) = case (maxViewSure kr xr rl rr) of
    λ {
      (MaxViewCon km xm r') → MaxViewCon km xm (balanceL k x l r')
    }
{-# COMPILE AGDA2HS maxViewSure #-}

-- deleteFindMin : {k a : Set} → (map : Map k a) → {IsTrue (not (null map))} → ((k × a) × Map k a)
deleteFindMin Tip = (error "Map.deleteFindMin: can not return the minimal element of an empty map" , Tip)
deleteFindMin t@(Bin _ k x l r) = case (minViewSure k x l r) of
    λ {
      (MinViewCon km xm t) → ((km , xm) , t)
    }
{-# COMPILE AGDA2HS deleteFindMin #-}

-- deleteFindMax : {k a : Set} → (map : Map k a) → {IsTrue (not (null map))} → ((k × a) × Map k a)
deleteFindMax Tip = (error "Map.deleteFindMax: can not return the maximal element of an empty map" , Tip)
deleteFindMax t@(Bin _ k x l r) = case (maxViewSure k x l r) of
    λ {
      (MaxViewCon km xm t) → ((km , xm) , t)
    }
{-# COMPILE AGDA2HS deleteFindMax #-}


{-------------------
  Balance
-------------------}

-- balance : {k a : Set} → k → a → Map k a → Map k a → Map k a
balance k x Tip Tip                 = Bin 1 k x Tip Tip
balance k x Tip r@(Bin _ _ _ Tip Tip) = Bin 2 k x Tip r
balance k x Tip r@(Bin _ rk rx Tip rr@(Bin _ _ _ _ _))  = Bin 3 rk rx (Bin 1 k x Tip Tip) rr
balance k x Tip r@(Bin _ rk rx (Bin _ rlk rlx _ _) Tip) = Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
balance k x Tip r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =
    if (rls < (ratio * rrs))
    then (Bin (1 + rs) rk rx (Bin (1 + rls) k x Tip rl) rr)
    else (Bin (1 + rs) rlk rlx (Bin (1 + size rll) k x Tip rll) (Bin (1 + rrs + size rlr) rk rx rlr rr))

balance k x l@(Bin ls lk lx ll lr) Tip = case (ll , lr) of
          λ {
            (Tip , Tip) -> Bin 2 k x l Tip
          ; (Tip , (Bin _ lrk lrx _ _)) -> Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
          ; ((Bin _ _ _ _ _) , Tip) -> Bin 3 lk lx ll (Bin 1 k x Tip Tip)
          ; ((Bin lls _ _ _ _) , (Bin lrs lrk lrx lrl lrr)) ->
              if (lrs < (ratio * lls))
              then (Bin (1 + ls) lk lx ll (Bin (1 + lrs) k x lr Tip))
              else (Bin (1 + ls) lrk lrx (Bin (1 + lls + size lrl) lk lx ll lrl) (Bin (1 + size lrr) k x lrr Tip))
          }
balance k x l@(Bin ls lk lx ll lr) r@(Bin rs rk rx rl rr) =
    if (rs > delta * ls)
    then (case (rl , rr) of
        λ {
          (Bin rls rlk rlx rll rlr , Bin rrs _ _ _ _) ->
            if (rls < ratio * rrs)
            then (Bin (1 + ls + rs) rk rx (Bin (1 + ls + rls) k x l rl) rr)
            else (Bin (1 + ls + rs) rlk rlx (Bin (1 + ls + size rll) k x l rll) (Bin (1 + rrs + size rlr) rk rx rlr rr))
        ; (_ , _) -> error "Failure in Data.Map.balance"
        })
    else (if (ls > delta * rs)
          then (case (ll , lr) of
              λ {
                (Bin lls _ _ _ _ , Bin lrs lrk lrx lrl lrr) ->
                  if (lrs < ratio * lls)
                  then (Bin (1 + ls + rs) lk lx ll (Bin (1 + rs + lrs) k x lr r))
                  else (Bin (1 + ls + rs) lrk lrx (Bin (1 + lls + size lrl) lk lx ll lrl) (Bin (1 + rs + size lrr) k x lrr r))
              ; (_ , _) -> error "Failure in Data.Map.balance"
              })
          else (Bin (1 + ls + rs) k x l r))


-- balanceL : {k a : Set} → k → a → Map k a → Map k a → Map k a

-- balanceR : {k a : Set} → k → a → Map k a → Map k a → Map k a


{-------------------
  bin
-------------------}

-- bin : {k a : Set} → k → a → Map k a → Map k a → Map k a
bin k x l r = let sl = size l
                  sr = size r
              in (Bin (size l + size r + 1)
                  {additionPos sl sr {sizeIsPos l} {sizeIsPos r}}
                  k x l r)


{-------------------
  Eq
-------------------}

instance
  iEqMap : {k a : Set} ⦃ _ : Eq k ⦄ ⦃ _ : Eq a ⦄ → Eq (Map k a)
  iEqMap ._==_ t1 t2 = (size t1 == size t2) && (toAscList t1 == toAscList t2)


{-------------------
  Ord
-------------------}

instance
  iOrdMap : {k a : Set} ⦃ _ : Ord k ⦄ ⦃ _ : Ord a ⦄ → Ord (Map k a)
  iOrdMap = ordFromCompare (λ t1 t2 → compare (toAscList t1) (toAscList t2))


{-------------------
  splitRoot
-------------------}

-- splitRoot : {k a : Set} → Map k a → List (Map k a)
splitRoot orig = case orig of
  λ {
    Tip             -> []
  ; (Bin _ k v l r) -> l ∷ (singleton k v) ∷ r ∷ []
  }
