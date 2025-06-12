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

module Lists where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Singletons
import Data.Singletons.TH

import TemplateTypeRec

$(recursiveTypes [d|
    data TP a = FF a | HomList [TypeDummy]
        deriving (Eq, Ord, Show)
    |])

example :: GetTP Integer (HomList (HomList FF))
example = [[1,2,3], [4,5,6]]

flattens :: STP t -> GetTP a t -> GetTP a (HomList FF)
flattens t l = case t of
    SFF -> [l]
    SHomList SFF -> l
    SHomList (SHomList t) -> flattens (SHomList t) (concat l)

example' :: GetTP Integer (HomList FF)
example' = flattens (SHomList (SHomList (SHomList SFF))) [[[1],[2],[3]],[[4],[5],[6]]]

{-
flatten :: SingTP t => GetTP a t -> GetTP a (HomList FF)
flatten = flattens singTP
---}

{-
$(singletons [d| 
    data TP' = FF' | HList' [TP']
    |])
---}


data HTP a = HFF | HList [HTP a]
    deriving (Eq, Ord, Show)

data SHTP (a :: HTP t) where
    SHFF :: SHTP HFF
    SHNil :: SHTP (HList '[])
    SHCons :: SHTP a -> SHTP (HList t) -> SHTP (HList (a:t))

deriving instance Show (SHTP a)
deriving instance Eq (SHTP a)
deriving instance Ord (SHTP a)

type family GetHTP a (t :: HTP a)
type instance GetHTP a HFF = a
type instance GetHTP a (HList '[]) = ()
type instance GetHTP a (HList (h:t)) = (GetHTP a h, GetHTP a (HList t))

hhead :: GetHTP a (HList (x:xs)) -> GetHTP a x
hhead (x, xs) = x

htail :: GetHTP a (HList (x:xs)) -> GetHTP a (HList xs)
htail (x, xs) = xs 

type family AppendType (h :: HTP a) (t :: HTP a) :: HTP a where
    AppendType x HFF = HList [x, HFF]
    AppendType x (HList xs) = HList (x:xs)

sAppendType :: SHTP h -> SHTP t -> SHTP (AppendType h t)
sAppendType x SHFF = SHCons x (SHCons SHFF SHNil)
sAppendType x SHNil = SHCons x SHNil
sAppendType x (SHCons a b) = SHCons x (SHCons a b)

happend :: SHTP h -> SHTP t -> GetHTP a h -> GetHTP a t -> GetHTP a (AppendType h t)
happend th tt h t = case tt of
    SHFF -> (h, (t, ()))
    SHNil -> (h, t)
    SHCons _ _ -> (h, t)

type family ConcatType (x :: HTP a) (y :: HTP a) :: HTP a where
    ConcatType HFF (HList ys) = HList (HFF:ys)
    ConcatType (HList '[]) (HList ys) = HList ys
    ConcatType (HList (x:xs)) (HList ys) = AppendType x (ConcatType (HList xs) (HList ys))
    ConcatType a HFF = ConcatType a (HList '[HFF])

sConcatType :: SHTP x -> SHTP y -> SHTP (ConcatType x y)
sConcatType SHFF SHNil = SHCons SHFF SHNil
sConcatType SHFF (SHCons a b) = SHCons SHFF (SHCons a b)
sConcatType SHNil SHNil = SHNil
sConcatType SHNil (SHCons a b) = SHCons a b
sConcatType (SHCons x xs) SHNil = sAppendType x (sConcatType xs SHNil)
sConcatType (SHCons x xs) (SHCons a b) = sAppendType x (sConcatType xs (SHCons a b))
sConcatType a SHFF = sConcatType a (SHCons SHFF SHNil)

hconcat :: SHTP x -> SHTP hly -> GetHTP a x -> GetHTP a hly -> GetHTP a (ConcatType x hly)
hconcat tx SHFF x y = hconcat tx (SHCons SHFF SHNil) x (y, ())
hconcat tx (ty@(SHCons tya tyb)) x y = case tx of
    SHFF -> (x, y)
    SHNil -> y
    SHCons th tt -> 
        let (h, t) = x 
            aux :: SHTP th -> SHTP (HList tt) -> SHTP (HList ty) -> GetHTP a th -> GetHTP a (HList tt) -> GetHTP a (HList ty) -> GetHTP a (AppendType th (ConcatType (HList (tt)) (HList ty)))
            aux th tt ty h t y = happend th (sConcatType tt ty) h (hconcat tt ty t y) in 
            
            aux th tt ty h t y 
hconcat tx (ty@(SHNil)) x y = case tx of
    SHFF -> (x, y)
    SHNil -> y
    SHCons th tt -> 
        let (h, t) = x 
            aux :: SHTP th -> SHTP (HList tt) -> SHTP (HList ty) -> GetHTP a th -> GetHTP a (HList tt) -> GetHTP a (HList ty) -> GetHTP a (AppendType th (ConcatType (HList (tt)) (HList ty)))
            aux th tt ty h t y = happend th (sConcatType tt ty) h (hconcat tt ty t y) in 
            
            aux th tt ty h t y 

type family FlattenType (t :: HTP a) :: HTP a where
    FlattenType HFF = HFF
    FlattenType (HList '[]) = HList '[]
    FlattenType (HList (HFF:xs)) = AppendType HFF (FlattenType (HList xs))
    FlattenType (HList ((HList hs):xs)) = ConcatType (FlattenType (HList hs)) (FlattenType (HList xs))

sFlattenType :: SHTP x -> SHTP (FlattenType x)
sFlattenType SHFF = SHFF
sFlattenType SHNil = SHNil
sFlattenType (SHCons SHFF xs) = sAppendType SHFF (sFlattenType xs)
sFlattenType (SHCons SHNil xs) = sConcatType SHNil $ sFlattenType xs
sFlattenType (SHCons (SHCons h hs) xs) = sConcatType (sFlattenType (SHCons h hs)) (sFlattenType xs)


aux :: SHTP (HList th) -> SHTP (HList tx) -> GetHTP a (HList th) -> GetHTP a (HList tx) -> 
    GetHTP a (ConcatType (FlattenType (HList th)) (FlattenType (HList tx))) 
aux th tx h t = 
    hconcat (sFlattenType th) (sFlattenType tx) (hflatten th h) (hflatten tx t)


hflatten :: SHTP x -> GetHTP a x -> GetHTP a (FlattenType x)
hflatten tx x = case tx of
    SHFF -> x
    SHNil -> x
    SHCons SHFF xs -> 
        let (h, t) = x in happend SHFF (sFlattenType xs) h (hflatten xs t)
    SHCons SHNil xs ->
        let (h, t) = x in 
            aux SHNil xs h t
    SHCons (SHCons h hs) xs ->
        let ((hh, th), t) = x in 
            aux (SHCons h hs) xs (hh, th) t


-- Example
list1 :: GetHTP Integer (HList '[])
list1 = ()
slist1 :: SHTP (HList '[])
slist1 = SHNil

list2 :: GetHTP Integer (HList '[HFF])
list2 = (5, ())
slist2 :: SHTP (HList '[HFF])
slist2 = SHCons SHFF SHNil

list3 :: GetHTP Integer (HList '[HFF, HList '[], HList '[HFF]])
list3 = (3, (list1, (list2, ())))
slist3 :: SHTP (HList '[HFF, HList '[], HList '[HFF]])
slist3 = SHCons SHFF (SHCons slist1 (SHCons slist2 SHNil))

flatlist3 :: GetHTP Integer (HList '[HFF, HFF])
flatlist3 = hflatten slist3 list3