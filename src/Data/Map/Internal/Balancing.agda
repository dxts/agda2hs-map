{-# OPTIONS --warning noMissingDefinitions #-}

module Data.Map.Internal.Balancing where

open import Haskell.Prelude
{-# FOREIGN AGDA2HS
import Prelude
#-}

open import Data.Map.Internal.Datatype
{-# FOREIGN AGDA2HS
import Data.Map.Internal.Datatype
#-}

delta : Nat
delta = 3

ratio : Nat
ratio = 2

module Balancing {k a : Set} ⦃ iOrdk : Ord k ⦄ where

  balance : (kx : k) → a → Map k a  → Map k a → Map k a
  balance k x Tip Tip                   = Bin 1 k x Tip Tip
  balance k x Tip r@(Bin _ _ _ Tip Tip) = bin k x Tip r
  balance k x Tip r@(Bin _ rk rx Tip rr@(Bin _ _ _ _ _))     = bin rk rx (Bin 1 k x Tip Tip) rr
  balance k x Tip r@(Bin _ rk rx rl@(Bin _ rlk rlx _ _) Tip) = bin rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
  balance k x Tip r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =
      if (rls < (ratio * rrs))
      then (bin rk rx (bin k x Tip rl) rr)
      else (bin rlk rlx (bin k x Tip rll) (bin rk rx rlr rr))

  balance k x l@(Bin ls lk lx Tip Tip)                    Tip = bin k x l Tip
  balance k x l@(Bin ls lk lx Tip lr@(Bin _ lrk lrx _ _)) Tip = bin lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
  balance k x l@(Bin ls lk lx ll@(Bin _ _ _ _ _) Tip)     Tip = bin lk lx ll (Bin 1 k x Tip Tip)
  balance k x l@(Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr)) Tip =
      if (lrs < (ratio * lls))
      then (bin lk lx ll (bin k x lr Tip))
      else (bin lrk lrx (bin lk lx ll lrl) (bin k x lrr Tip))

  balance k x l@(Bin ls lk lx ll@(Bin lls _ _ _ _ ) lr@(Bin lrs lrk lrx lrl lrr)) r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =
      if (rs > delta * ls)
      then (if (rls < ratio * rrs)
            then (bin rk rx (bin k x l rl) rr)
            else (bin rlk rlx (bin k x l rll) (bin rk rx rlr rr)))
      else (if (ls > delta * rs)
            then (if (lrs < ratio * lls)
                  then (bin lk lx ll (bin k x lr r))
                  else (bin lrk lrx (bin lk lx ll lrl) (bin k x lrr r)))
            else (bin k x l r)
          )
  balance k x l@(Bin ls lk lx ll@(Bin lls _ _ _ _ ) lr@(Bin lrs lrk lrx lrl lrr)) r@(Bin rs rk rx rl rr) =
      if (ls > delta * rs)
      then (if (lrs < ratio * lls)
            then (bin lk lx ll (bin k x lr r))
            else (bin lrk lrx (bin lk lx ll lrl) (bin k x lrr r)))
      else (bin k x l r)
  balance k x l@(Bin ls lk lx ll lr) r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =
      if (rs > delta * ls)
      then (if (rls < ratio * rrs)
            then (bin rk rx (bin k x l rl) rr)
            else (bin rlk rlx (bin k x l rll) (bin rk rx rlr rr)))
      else (bin k x l r)
  balance k x l@(Bin ls lk lx ll lr) r@(Bin rs rk rx rl rr) = (bin k x l r)
  {-# COMPILE AGDA2HS balance #-}

  balanceL : (kx : k) → a → Map k a → Map k a → Map k a
  balanceL k x Tip Tip = bin k x Tip Tip
  balanceL k x l@(Bin _ _ _ Tip Tip) Tip = bin k x l Tip
  balanceL k x l@(Bin _ lk lx Tip (Bin _ lrk lrx _ _)) Tip = bin lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
  balanceL k x l@(Bin _ lk lx ll@(Bin _ _ _ _ _) Tip) Tip = bin lk lx ll (Bin 1 k x Tip Tip)
  balanceL k x l@(Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr)) Tip =
    if (lrs < ratio * lls)
    then (bin lk lx ll (bin k x lr Tip))
    else (bin lrk lrx (bin lk lx ll lrl) (bin k x lrr Tip))

  balanceL k x Tip r@(Bin rs _ _ _ _) =  bin k x Tip r

  balanceL k x l@(Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr)) r@(Bin rs _ _ _ _) =
    if (ls > delta * rs)
    then (if (lrs < ratio * lls)
          then (bin lk lx ll (bin k x lr r))
          else (bin lrk lrx (bin lk lx ll lrl) (bin k x lrr r)))
    else (bin k x l r)

  balanceL k x l@(Bin ls lk lx ll@(Bin lls _ _ _ _) lr@Tip) r@(Bin rs _ _ _ _) =
    if (ls > delta * rs)
    then (bin lk lx ll (bin k x lr r))
    else (bin k x l r)

  balanceL k x l@(Bin ls lk lx ll@Tip lr@(Bin lrs lrk lrx lrl lrr)) r@(Bin rs _ _ _ _) =
    if (ls > delta * rs)
    then (bin lrk lrx (bin lk lx ll lrl) (bin k x lrr r))
    else (bin k x l r)

  balanceL k x l@(Bin ls lk lx ll@Tip lr@Tip) r@(Bin rs _ _ _ _) = bin k x l r
  {-# COMPILE AGDA2HS balanceL #-}

  balanceR : (kx : k) → a → Map k a → Map k a → Map k a
  balanceR k x Tip Tip = bin k x Tip Tip
  balanceR k x Tip r@(Bin _ _ _ Tip Tip) = bin k x Tip r
  balanceR k x Tip r@(Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) = bin rk rx (Bin 1 k x Tip Tip) rr
  balanceR k x Tip r@(Bin _ rk rx (Bin _ rlk rlx _ _) Tip) = bin rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
  balanceR k x Tip r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =
    if (rls < ratio * rrs)
    then (bin rk rx (bin k x Tip rl) rr)
    else (bin rlk rlx (bin k x Tip rll) (bin rk rx rlr rr))

  balanceR k x l@(Bin ls _ _ _ _) Tip = bin k x l Tip
  balanceR k x l@(Bin ls _ _ _ _) r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _)) =
    if (rs > delta * ls)
    then (if (rls < ratio * rrs)
          then (bin rk rx (bin k x l rl) rr)
          else (bin rlk rlx (bin k x l rll) (bin rk rx rlr rr)))
    else (bin k x l r)

  balanceR k x l@(Bin ls _ _ _ _) r@(Bin rs rk rx rl@Tip rr@(Bin rrs _ _ _ _)) =
    if (rs > delta * ls)
    then (bin rk rx (bin k x l rl) rr)
    else (bin k x l r)

  balanceR k x l@(Bin ls _ _ _ _) r@(Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@Tip) =
    if (rs > delta * ls)
    then (bin rlk rlx (bin k x l rll) (bin rk rx rlr rr))
    else (bin k x l r)

  balanceR k x l@(Bin ls _ _ _ _) r@(Bin rs rk rx rl@Tip rr@Tip) = bin k x l r
  {-# COMPILE AGDA2HS balanceR #-}


open Balancing public
