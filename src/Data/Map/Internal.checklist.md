
######   Query


```Haskell
null : {k a : Set} → Map k a → Bool
```

```Haskell
size : {k a : Set} → Map k a → Int
```

```Haskell
lookup : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe a
```

```Haskell
member : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Bool
```

```Haskell
notMember : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Bool
```

```Haskell
find : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → a
```

```Haskell
findWithDefault : {k a : Set} → ⦃ Ord k ⦄ → a → k → Map k a → a
```

```Haskell
lookupLT : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
```

```Haskell
lookupGT : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
```

```Haskell
lookupLE : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
```

```Haskell
lookupGE : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe (k × a)
```


######   Operators


```Haskell
\_!\_ :  {k a : Set} → ⦃ kOrd : Ord k ⦄ → (map : Map k a) → (key : k) → {Holds (member ⦃ kOrd ⦄ key map)} → a
```

```Haskell
\_!?\_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a → k → Maybe a
```

```Haskell
\_\\\\\_ : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Map k a
```



######   Construction


```Haskell
empty : {k a : Set} → Map k a
```

```Haskell
singleton : {k a : Set} → k → a → Map k a
```


######   Insertion


```Haskell
insert : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
```

```Haskell
insertR : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → k → a → (m : Map k a) → Map k a
```

```Haskell
insertWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a
```

```Haskell
insertWithR : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → k → a → Map k a → Map k a
```

```Haskell
insertWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a
```

```Haskell
insertWithKeyR : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → Map k a
```

```Haskell
insertLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → k → a → Map k a → (Maybe a × Map k a)
```



######   Deletion


```Haskell
delete : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq (Map k a) ⦄ → k → Map k a → Map k a
```

```Haskell
adjust : {k a : Set} → ⦃ Ord k ⦄ → (a → a) → k → Map k a → Map k a
```

```Haskell
adjustWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a) → k → Map k a → Map k a
```

```Haskell
update : {k a : Set} → ⦃ Ord k ⦄ → (a → Maybe a) → k → Map k a → Map k a
```

```Haskell
updateWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → Map k a
```

```Haskell
updateLookupWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → Maybe a) → k → Map k a → (Maybe a × Map k a)
```

```Haskell
alter : {k a : Set} → ⦃ Ord k ⦄ → (Maybe a → Maybe a) → k → Map k a → Map k a
```

-- [TODO] `alterF` and related methods



######   Indexing


```Haskell
findIndex : {k a : Set} → ⦃ kOrd : Ord k ⦄ → (key : k) → (map : Map k a) → {Holds (member ⦃ kOrd ⦄ key map)} → Int
```

```Haskell
lookupIndex : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → Maybe Int
```

```Haskell
elemAt : {k a : Set} → (n : Int) → (map : Map k a) → {Holds ((size map) > 0)} → k × a
```

```Haskell
take : {k a : Set} →  Int → Map k a → Map k a
```

```Haskell
drop : {k a : Set} →  Int → Map k a → Map k a
```

```Haskell
splitAt : {k a : Set} →  Int → Map k a → (Map k a × Map k a)
```

```Haskell
updateAt : {k a : Set} → (k → a → Maybe a) → Int → (map : Map k a) → {Holds ((size map) > 0)} → Map k a
```

```Haskell
deleteAt : {k a : Set} → Int → (map : Map k a) → {Holds ((size map) > 0)} → Map k a
```



######   Minimal, Maximal


```Haskell
lookupMinSure : {k a : Set} → k → a → Map k a → k × a
```

```Haskell
lookupMin : {k a : Set} → Map k a → Maybe (k × a)
```

```Haskell
findMin : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → k × a
```

```Haskell
lookupMaxSure : {k a : Set} → k → a → Map k a → k × a
```

```Haskell
lookupMax : {k a : Set} → Map k a → Maybe (k × a)
```

```Haskell
findMax : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → k × a
```

```Haskell
deleteMin : {k a : Set} → Map k a → Map k a
```

```Haskell
deleteMax : {k a : Set} → Map k a → Map k a
```

```Haskell
updateMin : {k a : Set} → (a → Maybe a) → Map k a → Map k a
```

```Haskell
updateMax : {k a : Set} → (a → Maybe a) → Map k a → Map k a
```

```Haskell
updateMinWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a
```

```Haskell
updateMaxWithKey : {k a : Set} → (k → a → Maybe a) → Map k a → Map k a
```

```Haskell
minViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)
```

```Haskell
maxViewWithKey : {k a : Set} → Map k a → Maybe ((k × a) × Map k a)
```

```Haskell
minView : {k a : Set} → Map k a → Maybe (a × Map k a)
```

```Haskell
maxView : {k a : Set} → Map k a → Maybe (a × Map k a)
```



######   Union


```Haskell
unions : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → f (Map k a) → Map k a
```

```Haskell
unionsWith : {k a : Set} → ⦃ Foldable f ⦄ → ⦃ Ord k ⦄ → (a → a → a) → f (Map k a) → Map k a
```

```Haskell
union : {k a : Set} → ⦃ Ord k ⦄ → ⦃ Eq a ⦄ → ⦃ Eq (Map k a) ⦄ → Map k a → Map k a → Map k a
```


######   Union with a combining function.


```Haskell
unionWith : {k a : Set} → ⦃ Ord k ⦄ → (a → a → a) → Map k a → Map k a → Map k a
```

```Haskell
unionWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → a → a) → Map k a → Map k a → Map k a
```


######   Difference


```Haskell
difference : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Map k a
```

```Haskell
withoutKeys : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Sett k → Map k a
```

```Haskell
differenceWith : {k a : Set} → ⦃ Ord k ⦄ → (a → b → Maybe a) → Map k a → Map k b → Map k a
```

```Haskell
differenceWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → b → Maybe a) → Map k a → Map k b → Map k a
```


######   Intersection


```Haskell
intersection : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Map k a
```

```Haskell
restrictKeys : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Sett k → Map k a
```

```Haskell
intersectionWith : {k a : Set} → ⦃ Ord k ⦄ → (a → b → c) → Map k a → Map k b → Map k c
```

```Haskell
intersectionWithKey : {k a : Set} → ⦃ Ord k ⦄ → (k → a → b → c) → Map k a → Map k b → Map k c
```



######   Disjoint


```Haskell
disjoint : {k a : Set} → ⦃ Ord k ⦄ → Map k a → Map k b → Bool
```



######   Compose


```Haskell
compose : ⦃ Ord b ⦄ → Map b c → Map a b → Map a c
```


######   merge


-- [TODO] `merge` function and it's helpers.

```Haskell
mergeWithKey : ⦃ Ord b ⦄ → (k → a → b → Maybe c) → (Map k a → Map k c) → (Map k b → Map k c) → Map k a → Map k b → Map k c
```



######   split


```Haskell
split : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Map k a)
```

```Haskell
splitLookup : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Maybe a × Map k a)
```

```Haskell
splitMember : {k a : Set} → ⦃ Ord k ⦄ → k → Map k a → (Map k a × Bool × Map k a)
```


######   link


```Haskell
link : {k a : Set} → k → a → Map k a → Map k a → Map k a
```

```Haskell
insertMax : {k a : Set} → k → a → Map k a → Map k a
```

```Haskell
insertMin : {k a : Set} → k → a → Map k a → Map k a
```



######   link2


```Haskell
link2 : {k a : Set} → Map k a → Map k a → Map k a
```



######   glue


```Haskell
glue : {k a : Set} → Map k a → Map k a → Map k a
```


```Haskell
data MinView (k : Set) (a : Set) : Set where
  MinViewCon : k → a → (Map k a) → MinView k a
```

```Haskell
data MaxView (k : Set) (a : Set) : Set where
  MaxViewCon : k → a → (Map k a) → MaxView k a
```

```Haskell
minViewSure : {k a : Set} → k → a → Map k a → Map k a → MinView k a
```

```Haskell
maxViewSure : {k a : Set} → k → a → Map k a → Map k a → MaxView k a
```

```Haskell
deleteFindMin : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → ((k × a) × Map k a)
```

```Haskell
deleteFindMax : {k a : Set} → (map : Map k a) → {Holds (size map > 0)} → ((k × a) × Map k a)
```



######   balance


```Haskell
balance : {k a : Set} → k → a → Map k a → Map k a → Map k a
```

```Haskell
balanceL : {k a : Set} → k → a → Map k a → Map k a → Map k a
```

```Haskell
balanceR : {k a : Set} → k → a → Map k a → Map k a → Map k a
```



######   bin


```Haskell
bin : {k a : Set} → k → a → Map k a → Map k a → Map k a
```



######   splitRoot


```Haskell
splitRoot : {k a : Set} → Map k a → List (Map k a)
```
