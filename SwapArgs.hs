{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE EmptyCase #-}

module SwapArgs where

import Data.Singletons
import Data.Singletons.TH
import Data.Void
import Data.Type.Equality

import TemplateTypeRec

$(recursiveTypes [d|
    data IType (a :: *) = FF a | (:->) (TypeDummy -> TypeDummy)
        deriving Show
    |])

type family LastArg (t :: IType k) where
    LastArg (t :-> FF) = t
    LastArg (t :-> (ta :-> tb)) = LastArg (ta :-> tb)

sLastArg :: SIType a -> SIType (LastArg a)
sLastArg t = case t of
    SFF -> undefined
    t :%-> SFF -> t
    t :%-> (ta :%-> tb) -> sLastArg (ta :%-> tb)

type family SwapLastArg (for :: IType k) (t :: IType k) where
    SwapLastArg for FF = FF
    SwapLastArg for (arg :-> FF) = for :-> FF
    SwapLastArg for (arg :-> (ta :-> tb)) = arg :-> (SwapLastArg for (ta :-> tb))

sSwapLastArg :: SIType for -> SIType t -> SIType (SwapLastArg for t)
sSwapLastArg for t = case t of
    SFF -> SFF
    arg :%-> SFF -> for :%-> SFF
    arg :%-> (ta :%-> tb) -> arg :%-> (sSwapLastArg for (ta :%-> tb))

type family SwapFirstLast (t :: IType k) where
    SwapFirstLast FF = FF
    SwapFirstLast (t :-> FF) = t :-> FF
    SwapFirstLast (t :-> (ta :-> tb)) = (LastArg (ta :-> tb)) :-> (SwapLastArg t (ta :-> tb))

sSwapFirstLast :: SIType t -> SIType (SwapFirstLast t)
sSwapFirstLast t = case t of
    SFF -> SFF
    (t :%-> SFF) -> t :%-> SFF
    (t :%-> (ta :%-> tb)) -> (sLastArg (ta :%-> tb)) :%-> (sSwapLastArg t (ta :%-> tb))

swapInArg :: SIType t -> SIType ta -> SIType tb -> GetIType k (LastArg (ta :-> tb)) -> GetIType k (t :-> (ta :-> tb)) -> GetIType k (SwapLastArg t (ta :-> tb))
swapInArg t ta tb xn fxi = case tb of
    SFF -> \x1 -> fxi x1 xn
    tx :%-> ty -> \xi -> swapInArg t tx ty xn (\t -> fxi t xi)

swapFirstLast :: SIType t -> GetIType k t -> GetIType k (SwapFirstLast t)
swapFirstLast t f = case t of
    SFF -> f
    t :%-> SFF -> f
    t :%-> (ta :%-> tb) -> \xn -> swapInArg t ta tb xn f 

-- We want to apply some preprocessing, like negating the value,
-- on the last argument of a variadic f. We could do it by induction,
-- but here we show a tool that helps do it more cleanly: we swap the
-- first and last argument, then we do the preprocessing on the first,
-- then we swap them back.
negateValue :: SIType t -> GetIType Integer t -> GetIType Integer t
negateValue t f = case t of
    SFF -> -f
    t1 :%-> t2 -> \x -> negateValue t2 (f x)
negateFirstArg :: SIType t -> GetIType Integer t -> GetIType Integer t
negateFirstArg t f = case t of
    t1 :%-> t2 -> \x -> f (negateValue t1 x)
    SFF -> f
negateLastArg :: SIType t1 -> SIType t2 -> GetIType Integer (t1 :-> t2) -> GetIType Integer (SwapFirstLast (SwapFirstLast (t1 :-> t2)))
negateLastArg t1 t2 f = swapFirstLast (sSwapFirstLast (t1 :%-> t2)) $ negateFirstArg (sSwapFirstLast (t1 :%-> t2)) $ swapFirstLast (t1 :%-> t2) f
-- Only issue is the result type has these two swaps. We need a lemma to get rid of them.


swapLastIdempotent :: SIType t -> SIType ta -> SIType tb -> SwapLastArg (LastArg (ta :-> tb)) (ta :-> tb) :~: ta :-> tb
swapLastIdempotent t ta tb = case tb of
    SFF -> Refl
    tx :%-> ty -> case swapLastIdempotent t tx ty of
        Refl -> Refl



swapswap :: SIType ta -> SIType tb -> SIType t1 -> SIType t2 -> SwapLastArg t1 (SwapLastArg t2 (ta :-> tb)) :~: SwapLastArg t1 (ta :-> tb)
swapswap ta tb t1 t2 = case tb of
    SFF -> Refl
    tx :%-> ty -> swapswapLemma ta tx ty t1 t2

swapswapLemma :: SIType ta -> SIType tx -> SIType ty -> SIType t1 -> SIType t2 -> SwapLastArg t1 (ta :-> SwapLastArg t2 (tx :-> ty)) :~: ta :-> SwapLastArg t1 (tx :-> ty) 
swapswapLemma ta tx ty t1 t2 = case ty of
    SFF -> Refl
    t :%-> t' -> case swapswap tx ty t1 t2 of
        Refl -> Refl



doubleflip :: SIType t -> SwapFirstLast (SwapFirstLast t) :~: t
doubleflip typ = case typ of
    SFF -> Refl
    t :%-> SFF -> Refl
    t :%-> (ta :%-> tb) -> lemma t ta tb

lemma :: SIType t -> SIType ta -> SIType tb -> SwapFirstLast ((LastArg (ta :-> tb)) :-> (SwapLastArg t (ta :-> tb))) :~: t :-> (ta :-> tb)
lemma t ta tb = case tb of
    SFF -> Refl
    tx :%-> ty -> lemma0 t ta (tx :%-> ty) 

lemma0 :: SIType t -> SIType ta -> SIType tb -> LastArg (SwapLastArg t (ta :-> tb)) :-> SwapLastArg (LastArg (ta :-> tb)) (SwapLastArg t (ta :-> tb)) :~: t :-> (ta :-> tb)
lemma0 t ta tb = case (lemma1 t ta tb, lemma2 t ta tb) of
    (Refl, Refl) -> Refl

lemma1 :: SIType t -> SIType ta -> SIType tb -> LastArg (SwapLastArg t (ta :-> tb)) :~: t
lemma1 t ta tb = case tb of
    SFF -> Refl
    tx :%-> ty -> lemma1' t ta tx ty

lemma1' :: SIType t -> SIType ta -> SIType tx -> SIType ty -> LastArg (ta :-> SwapLastArg t (tx :-> ty)) :~: t
lemma1' t ta tx ty = case ty of
    SFF -> Refl
    t1 :%-> t2 -> lemma1 t tx ty

lemma2 :: SIType t -> SIType ta -> SIType tb -> SwapLastArg (LastArg (ta :-> tb)) (SwapLastArg t (ta :-> tb)) :~: (ta :-> tb)
lemma2 t ta tb = case (swapswap ta tb (sLastArg (ta :%-> tb)) t) of
    Refl -> case (swapLastIdempotent t ta tb) of
        Refl -> Refl

betterNegateLastArg :: SIType t1 -> SIType t2 -> GetIType Integer (t1 :-> t2) -> GetIType Integer (t1 :-> t2)
betterNegateLastArg t1 t2 f = case (doubleflip (t1 :%-> t2)) of
    Refl -> negateLastArg t1 t2 f