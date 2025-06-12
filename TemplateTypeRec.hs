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

module TemplateTypeRec where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TH.Options
import Control.Monad.State

-- mantra: if singletons doesn't support something,
-- then i don't have to

-- usage demonstrated in TemplateTypeRecUse
-- and other modules (Lists, CPS, SwapArgs)

data TypeDummy

recursiveTypes :: Q [Dec] -> Q [Dec]
recursiveTypes m = do
    tns <- m
    res <- mapM recursiveTypesDef tns
    return $ concat res 

makeTVType :: TyVarBndr flag -> Type
makeTVType (PlainTV name flag) = VarT name
makeTVType (KindedTV name flag kind) = VarT name

makeTypeAppRev :: Type -> [Type] -> Type
makeTypeAppRev n [] = n
makeTypeAppRev n (h:t) = AppT (makeTypeAppRev n t) h

makeTypeApp :: Type -> [Type] -> Type
makeTypeApp n = (makeTypeAppRev n) . reverse

countDummies :: Type -> Int
countDummies (ForallT tvs cxt typ) = countDummies typ
countDummies (ForallVisT tvs typ) = countDummies typ
countDummies (AppT typ1 typ2) = countDummies typ1 + countDummies typ2
countDummies (AppKindT typ kind) = countDummies typ
countDummies (SigT typ kind) = countDummies typ
countDummies (ConT name) = if name == ''TypeDummy then 1 else 0
countDummies (InfixT typ1 op typ2) = countDummies typ1 + countDummies typ2
countDummies (UInfixT typ1 op typ2) = countDummies typ1 + countDummies typ2
countDummies (ParensT typ) = countDummies typ
countDummies (ImplicitParamT str typ) = countDummies typ
countDummies _ = 0

makeRectypeCon :: Type -> Con -> Con
makeRectypeCon deftype (NormalC name [(bang, typ)]) = 
    NormalC name (replicate (countDummies typ) (bang, deftype))
makeRectypeCon deftype x = error $ "Illegal constructor: " ++ show x

makeDeriv :: Cxt -> Type -> DerivClause -> [Dec]
makeDeriv cxt typ (DerivClause strat derivs) =
    map (\cl -> StandaloneDerivD strat cxt (AppT cl typ)) derivs


substDummiesM :: (Name -> Type) -> Type -> State [Name] Type
substDummiesM gettype (ForallT tvs cxt typ) = fmap (ForallT tvs cxt) $ substDummiesM gettype typ
substDummiesM gettype (ForallVisT tvs typ) = fmap (ForallVisT tvs) $ substDummiesM gettype typ
substDummiesM gettype (AppT typ1 typ2) = do
    t1 <- substDummiesM gettype typ1
    t2 <- substDummiesM gettype typ2
    return $ AppT t1 t2
substDummiesM gettype (AppKindT typ kind) = fmap (\t -> AppKindT t kind) $ substDummiesM gettype typ
substDummiesM gettype (SigT typ kind) = fmap (\t -> SigT t kind) $ substDummiesM gettype typ
substDummiesM gettype (ConT name) = if name /= ''TypeDummy then return (ConT name) else do
    names <- get
    put (tail names)
    return (gettype (head names))
substDummiesM gettype (InfixT typ1 op typ2) = do
    t1 <- substDummiesM gettype typ1 
    t2 <- substDummiesM gettype typ2
    return $ InfixT t1 op t2
substDummiesM gettype (UInfixT typ1 op typ2) = do
    t1 <- substDummiesM gettype typ1 
    t2 <- substDummiesM gettype typ2
    return $ UInfixT t1 op t2
substDummiesM gettype (ParensT typ) = fmap ParensT $ substDummiesM gettype typ
substDummiesM gettype (ImplicitParamT str typ) = fmap (ImplicitParamT str) $ substDummiesM gettype typ
substDummiesM gettype x = return x

substDummies :: (Name -> Type) -> Type -> [Name] -> Type
substDummies gettype con = evalState (substDummiesM gettype con)

conToInstance :: Type -> Con -> Q Dec
conToInstance family (NormalC cname [(_, typ)]) = do
    vnames <- sequence (replicate (countDummies typ) (newName "t"))
    let gettype name = AppT family (VarT name)
    let substituted = substDummies gettype typ vnames
    return $ TySynInstD $ TySynEqn Nothing (AppT family $ makeTypeApp (PromotedT cname) (map VarT vnames)) substituted
conToInstance _ _ = error "shouldn't even be here"

multipleApply :: Exp -> Exp -> Int -> Exp
multipleApply e1 e2 0 = e1
multipleApply e1 e2 n = AppE (multipleApply e1 e2 (n - 1)) e2

newConToSingInstance :: Name -> Name -> Con -> Q Dec
newConToSingInstance singClassName singName (NormalC cname hs) = do
    vnames <- sequence (replicate (length hs) (newName "t"))
    let cxt = map (AppT (ConT singClassName) . VarT) vnames
    let instanceType = AppT (ConT singClassName) $ makeTypeApp (PromotedT cname) (map VarT vnames)
    let dec = ValD (VarP singName) (NormalB $ multipleApply (ConE $ singledDataConName defaultOptions cname) (VarE singName) (length hs)) []
    return $ InstanceD Nothing cxt instanceType [dec]
newConToSingInstance _ _ _ = error "definitely shouldn't be here"

injectivity :: [Type] -> Name -> Name -> Maybe InjectivityAnn
injectivity [] rname vname = Just $ InjectivityAnn rname [vname]
injectivity _ _ _ = Nothing

recursiveTypesDef :: Dec -> Q [Dec]
recursiveTypesDef (q@(DataD cxt name tyvars kind cons derivs)) = do
    let tvtypes = map makeTVType tyvars
    let deftype = makeTypeApp (ConT name) (tvtypes)
    let newcons = map (makeRectypeCon deftype) cons
    let decl = DataD cxt name tyvars kind newcons []
    
    vname <- newName "a"
    let singleName = singledDataConName defaultOptions name
    let standalonederivs = concat $ map (makeDeriv cxt deftype) derivs
    let singderivs = concat $ map (makeDeriv cxt (AppT (ConT singleName) (VarT vname))) derivs
    sings <- singletons (return [decl])

    vname <- newName "t"
    rname <- newName "r"
    let familyName = mkName $ "Get" ++ nameBase name
    let family = makeTypeApp (ConT familyName) (tvtypes)
    let familyDecl = [OpenTypeFamilyD (TypeFamilyHead familyName (tyvars ++ [KindedTV vname () deftype]) (TyVarSig (PlainTV rname ())) (injectivity tvtypes rname vname))]
    instanceDecls <- sequence $ map (conToInstance family) cons

    vname <- newName "t"
    let singClassName = mkName $ "Sing" ++ nameBase name
    let singName = mkName $ "sing" ++ nameBase name
    let classDecl = [ClassD [] singClassName [KindedTV vname () deftype] [] [SigD singName (AppT (ConT singleName) (VarT vname))]]
    singInstanceDecls <- sequence $ map (newConToSingInstance singClassName singName) newcons
    
    return (sings ++ standalonederivs ++ singderivs ++ familyDecl ++ instanceDecls ++ classDecl ++ singInstanceDecls)

recursiveTypesDef x = singletons (return [x])