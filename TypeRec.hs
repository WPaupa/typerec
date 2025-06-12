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

module TypeRec where

import Data.Singletons
import Data.Singletons.TH
import Data.Void
import Data.Type.Equality

$(singletons [d|
    data IType = FF | IType :-> IType | IType :* IType | IType :+ IType
    |])

deriving instance Show (IType)
deriving instance Eq (IType)
deriving instance Ord (IType)

deriving instance Show (SIType a)
deriving instance Eq (SIType a)
deriving instance Ord (SIType a)
-- note: this only works if standalone

-- this can be also set to void,
-- but integer is easier to debug
type Zero = Integer

-- note: injectivity
type family GetIType (t :: IType) = r | r -> t
type instance GetIType FF = Zero
type instance GetIType (t :-> t') = (GetIType t) -> (GetIType t')
type instance GetIType (t :* t') = (GetIType t, GetIType t')
type instance GetIType (t :+ t') = Either (GetIType t) (GetIType t')

-- we need the injectivity to make effective use of this class
class SingIType (t :: IType) where
    singIType :: SIType t

instance SingIType FF where
    singIType = SFF

instance (SingIType t, SingIType t') => SingIType (t :-> t') where
    singIType = singIType :%-> singIType

instance (SingIType t, SingIType t') => SingIType (t :* t') where
    singIType = singIType :%* singIType

instance (SingIType t, SingIType t') => SingIType (t :+ t') where
    singIType = singIType :%+ singIType

fromS :: SIType a -> IType
fromS x = case x of
    SFF -> FF
    a :%-> b -> fromS a :-> fromS b 
    a :%* b -> fromS a :* fromS b
    a :%+ b -> fromS a :+ fromS b
-- i don't think the other way can be typed sensibly

id_tp :: GetIType (t :-> t)
id_tp x = x

id_z :: GetIType (FF :-> FF)
id_z = id_tp @FF

-- note: we don't use the fact that FF = Void
exf :: SIType t -> GetIType (FF :-> t)
exf typ = case typ of
    SFF -> \x -> x
    t1 :%-> t2 -> \z b -> exf t2 z
    t1 :%+ t2 -> \z -> Left $ exf t1 z
    t1 :%* t2 -> \z -> (exf t1 z, exf t2 z)

-- here we use the injectivity
exfalso :: SingIType t => GetIType (FF :-> t)
exfalso = exf singIType

-- these are intuitionistically true (in other words, they type in regular Haskell)
dem :: GetIType (((t1 :-> FF) :* (t2 :-> FF)) :-> ((t1 :+ t2) :-> FF))
dem (f, g) (Left e) = f e
dem (f, g) (Right e) = g e

wel :: GetIType ((t1 :-> FF) :-> ((t1 :* t2) :-> FF))
wel f (a, b) = f a

wer :: GetIType ((t2 :-> FF) :-> ((t1 :* t2) :-> FF))
wer f (a, b) = f b

-- this one is intuitionistically false (wouldn't type in regular Haskell, without SIType)
tnd :: SIType t -> GetIType (t :+ (t :-> FF))
tnd typ = case typ of
    SFF -> Right (\x -> x)
    t1 :%-> t2 ->
        case (tnd t1, tnd t2) of
            (_ , Left e) -> Left (\x -> e)
            (Left e, Right f) -> Right (\h -> f (h e))
            (Right f1, Right f2) -> Left (\k -> exf t2 (f1 k))
    t1 :%+ t2 -> 
        case (tnd t1, tnd t2) of
            (_, Left e) -> Left (Right e)
            (Left e, _) -> Left (Left e)
            (Right f1, Right f2) -> Right (dem (f1, f2))
    t1 :%* t2 ->
        case (tnd t1, tnd t2) of
            (Right f, _) -> Right (wel f)
            (_, Right f) -> Right (wer f)
            (Left e1, Left e2) -> Left (e1, e2)

pei :: SIType t1 -> SIType t2 -> GetIType (((t1 :-> t2) :-> t1) :-> t1)
pei typ1 typ2 = case (tnd typ1, tnd (typ1 :%-> typ2)) of
    (Left e, _) -> \g -> e
    (Right f, Left e) -> \g -> g e
    (Right f1, Right f2) -> \g -> exf typ1 (f2 (\z -> exf typ2 (f1 z)))

peirce :: (SingIType t1, SingIType t2) => GetIType (((t1 :-> t2) :-> t1) :-> t1)
peirce = pei singIType singIType

type One = Zero -> Zero

-- however once we go back to Haskell types, we don't get anything new
example :: ((Zero -> One) -> Zero) -> Zero
example = peirce

-- In this part we need Zero = Integer
--{-
sumOfT :: SIType t1 -> GetIType (FF :-> t1)
sumOfT typ = case typ of
    SFF -> \x -> x
    SFF :%-> t2 -> \x y -> sumOfT t2 (x + y)
    _ -> error "Wrong type!"

sumOf :: SingIType t1 => GetIType (FF :-> t1)
sumOf = sumOfT singIType

stupidShowT :: SIType t1 -> GetIType t1 -> String
stupidShowT typ = case typ of
    SFF -> \x -> show x
    t1 :%-> t2 -> \x -> "Function of type " ++ show (fromS typ)
    t1 :%+ t2 -> 
        let aux (Left a) = "Left (" ++ stupidShowT t1 a ++ ")"
            aux (Right a) = "Right (" ++ stupidShowT t2 a ++ ")" in
        aux 
    t1 :%* t2 -> \(a, b) -> "(" ++ stupidShowT t1 a ++ ", " ++ stupidShowT t2 b ++ ")"

stupidShow :: SingIType t => GetIType t -> String
stupidShow = stupidShowT singIType


res :: String 
res = stupidShow ((5 :: Integer), \(x :: Integer) -> ((4 :: Integer), \(y :: Integer) -> (3 :: Integer)))
---}

-- Since our types represent classical logic, inhabitation is easy
-- The goal of this section if to make a function that,
-- for any inhabited type, will return its inhabitant

data Uninhabited :: IType -> * where
    UFF :: Uninhabited FF
    UAR :: (Uninhabited t1 -> Void) -> Uninhabited t2 -> Uninhabited (t1 :-> t2)
    UPL :: Uninhabited t1 -> Uninhabited t2 -> Uninhabited (t1 :+ t2)
    UML :: Uninhabited t1 -> Uninhabited (t1 :* t2)
    UMR :: Uninhabited t2 -> Uninhabited (t1 :* t2)

type Inhabited a = Uninhabited a -> Void

inhabitedOne :: Inhabited (FF :-> FF)
inhabitedOne (UAR iFF uFF) = iFF uFF

inhAR :: Inhabited t2 -> Inhabited (t1 :-> t2)
inhAR inht2 (UAR inht1 uninht2) = inht2 uninht2

inhAL :: Uninhabited t1 -> Inhabited (t1 :-> t2)
inhAL uninht1 (UAR inht1 uninht2) = inht1 uninht1

inhPL :: Inhabited t1 -> Inhabited (t1 :+ t2)
inhPL inht1 (UPL uninht1 uninht2) = inht1 uninht1

inhPR :: Inhabited t2 -> Inhabited (t1 :+ t2)
inhPR inht2 (UPL uninht1 uninht2) = inht2 uninht2

inhML :: Inhabited t1 -> Inhabited t2 -> Inhabited (t1 :* t2)
inhML inht1 inht2 (UML uninht1) = inht1 uninht1
inhML inht1 inht2 (UMR uninht2) = inht2 uninht2

-- Matching on owoto t will later be useful to check
-- if t is inhabited
owoto :: SIType t -> Either (Uninhabited t) (Inhabited t)
owoto typ = case typ of
    SFF -> Left UFF
    t1 :%-> t2 -> case (owoto t1, owoto t2) of
        (_, Right inh) -> Right $ inhAR inh
        (Left uninh, _) -> Right $ inhAL uninh
        (Right inht1, Left uninht2) -> Left $ UAR inht1 uninht2
    t1 :%+ t2 -> case (owoto t1, owoto t2) of
        (Left uninht1, Left uninht2) -> Left $ UPL uninht1 uninht2
        (_, Right inh) -> Right $ inhPR inh
        (Right inh, _) -> Right $ inhPL inh
    t1 :%* t2 -> case (owoto t1, owoto t2) of
        (Left uninh, _) -> Left $ UML uninh
        (_, Left uninh) -> Left $ UMR uninh
        (Right inht1, Right inht2) -> Right $ inhML inht1 inht2

owotoS :: SingIType t => Either (Uninhabited t) (Inhabited t)
owotoS = owoto singIType


uninhabitant :: SIType t -> Uninhabited t -> GetIType (t :-> FF)
uninhabitant typ uninh = case (typ, uninh) of
    (SFF, UFF) -> \x -> x
    (t1 :%-> t2, UAR inht1 uninht2) -> \f -> uninhabitant t2 uninht2 (f $ inhabitant t1 inht1)
    (t1 :%* t2, UML uninh) -> \(x1, x2) -> uninhabitant t1 uninh x1 
    (t1 :%* t2, UMR uninh) -> \(x1, x2) -> uninhabitant t2 uninh x2
    (t1 :%+ t2, UPL uninht1 uninht2) -> 
        let aux (Left x1) = uninhabitant t1 uninht1 x1
            aux (Right x2) = uninhabitant t2 uninht2 x2 in aux

inhabitant :: SIType t -> Inhabited t -> GetIType t
inhabitant typ inh = case typ of
    SFF -> case inh UFF of
    t1 :%-> t2 -> case (owoto t1, owoto t2) of
        (_, Right inh) -> \x -> inhabitant t2 inh
        (Left uninh, _) -> \x -> exf t2 $ uninhabitant t1 uninh x
        (Right inht1, Left uninht2) -> case inh (UAR inht1 uninht2) of
    t1 :%+ t2 -> case (owoto t1, owoto t2) of
        (Left uninht1, Left uninht2) -> case inh (UPL uninht1 uninht2) of
        (_, Right inh) -> Right $ inhabitant t2 inh
        (Right inh, _) -> Left $ inhabitant t1 inh
    t1 :%* t2 -> case (owoto t1, owoto t2) of
        (Left uninh, _) -> case inh (UML uninh) of
        (_, Left uninh) -> case inh (UMR uninh) of
        (Right inht1, Right inht2) -> (inhabitant t1 inht1, inhabitant t2 inht2)

uninhabitantS :: SingIType t => Uninhabited t -> GetIType (t :-> FF)
uninhabitantS = uninhabitant singIType

inhabitantS :: SingIType t => Inhabited t -> GetIType t
inhabitantS = inhabitant singIType

inhabitedTND :: SIType t -> Inhabited (t :+ (t :-> FF))
inhabitedTND t (UPL uninh (UAR inh UFF)) = inh uninh

inhabitantTND :: SingIType t => GetIType (t :+ (t :-> FF))
inhabitantTND = inhabitantS (inhabitedTND singIType)