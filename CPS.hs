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

module CPS where

import Data.Singletons
import Data.Singletons.TH
import Data.Void
import Data.Type.Equality

import TemplateTypeRec

$(recursiveTypes [d|
    data IType (a :: *) = FF a | (:->) (TypeDummy -> TypeDummy) | (:*) (TypeDummy, TypeDummy)
        deriving Show
    |])

-- Goal: a function converting any variadic f to continuation passing style.

type family CPS (a :: IType k) (t :: IType k) = (r :: IType k) | r -> t where
    CPS a FF = (FF :-> a) :-> a
    CPS a (t :-> t') = ((t :-> a) :-> a) :-> (CPS a t')
    CPS a (t :* t') = (CPS a t) :* (CPS a t')

-- intuition: the accumulator has the continuation of f x_1 ... x_i 
toCPSAcc :: SIType a -> SIType t -> GetIType k ((t :-> a) :-> a) -> GetIType k (CPS a t)
toCPSAcc a t acc = case t of
    SFF -> acc
    t1 :%* t2 -> (toCPSAcc a t1 (\k -> acc (\(t1, t2) -> k t1)), toCPSAcc a t2 (\k -> acc (\(t1, t2) -> k t2)))
    t1 :%-> t2 -> \cx -> toCPSAcc a t2 (\k -> cx (\x -> acc (\f -> k (f x))))

toCPS :: SIType a -> SIType t -> GetIType k t -> GetIType k (CPS a t)
toCPS a t f = toCPSAcc a t (\cx -> cx f)

f :: Integer -> Integer
f x = x + 1

fCPS :: ((Integer -> Integer) -> Integer) -> ((Integer -> Integer) -> Integer)
fCPS = toCPS SFF (SFF :%-> SFF) f

pita :: Integer -> Integer -> Integer
pita x y = x * x + y * y

pitaCPS = toCPS SFF (SFF :%-> (SFF :%-> SFF)) pita

pita34 :: Integer
pita34 = pitaCPS (\cx -> cx 3) (\cx -> cx 4) (\x -> x)