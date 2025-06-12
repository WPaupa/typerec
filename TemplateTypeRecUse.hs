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

module TemplateTypeRecUse where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Singletons
import Data.Singletons.TH

import TemplateTypeRec

-- This code generates exactly the type definitions
-- from TypeRec (all code up to line 64) 

type Zero = Integer

$(recursiveTypes [d| 
    data IType = FF Zero | (:->) (TypeDummy -> TypeDummy) | (:+) (Either TypeDummy TypeDummy) | (:*) (TypeDummy, TypeDummy)
        deriving (Eq, Ord, Show)
    |])

-- We can also do parametrized recursive types:
$(recursiveTypes [d|
    data TP a = FFa a | (:-->) (TypeDummy -> TypeDummy)
    |])