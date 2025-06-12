# Recursion on the shape of the type
This project has been created as coursework for [Advanced Functional Programming](https://github.com/mbenke/zpf2022/). It features:
- Type information available at runtime
- Functions representing [classical logic](#logic) (as opposed to intuitionistic)
- [Variadic functions](#variadic-functions) with operations like translation to continuation passing style and modifying the last argument
- [Heterogenous lists](#heterogenous-lists)
### Main idea
The idea is as demonstrated in `TypeRec.hs`. Let's say we have a base type `FF` and every other type we use is built from it using products (tuples), coproducts (`Either`) and functions. For every such type $t$, we have a function $f_t$ from `FF` to that type, which we can prove by induction. For example the function $f_{t_1\to t_2}$ will take the argument $z$ of type `FF` and return a constant function returning $f_{t_2}(z)$. However to write it in Haskell, we need a way to induce on the shape of the type. Let's say we have some argument of type `SIType t`, telling us about the shape of type `t`. The constructors of `SIType` are `SFF` for the base type, `t1 :%-> t2` for a function type from `t1` to `t2` and so on. We get the function:
```haskell
exf :: SIType t -> GetIType (FF :-> t)
exf typ = case typ of
    SFF -> \x -> x
    t1 :%-> t2 -> \z b -> exf t2 z
    t1 :%+ t2 -> \z -> Left $ exf t1 z
    t1 :%* t2 -> \z -> (exf t1 z, exf t2 z)
```

Here `t` and `FF :-> t` are of some kind `IType`, and `GetIType` is the function converting them to kind `*` (so, to a type). This is how the main logic works:

```haskell
$(singletons [d|
    data IType = FF | IType :-> IType | IType :* IType | IType :+ IType
    |])

type Zero = Integer
type family GetIType (t :: IType) = r | r -> t
type instance GetIType FF = Zero
type instance GetIType (t :-> t') = (GetIType t) -> (GetIType t')
type instance GetIType (t :* t') = (GetIType t, GetIType t')
type instance GetIType (t :+ t') = Either (GetIType t) (GetIType t')
```

We use type promotion to make a datakind that signifies our type, and the singletons library gives us the tools to use information on this datakind effectively in our functions.
### Class
Since the family `GetIType` is injective (note: this will stop being true when we start dealing with parametrized types), it is possible to deduce the shape of the type from just the type alone. That means that we don't need to explicitly pass the shape of the type, using classes:
```haskell
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
```
And then for example:
```haskell
exfalso :: SingIType t => GetIType (FF :-> t)
exfalso = exf singIType

example :: Integer -> (Integer, (Either Integer Integer))
example = exfalso
```
### Logic
Since we can base our decision if something of a coproduct (`Either`) type should be a `Left` or a `Right` on the shape of the type, we get access to classical tautologies forbidden by the Curry-Howard isomorphism:
```haskell
-- these are intuitionistically true (in other words, they type in regular Haskell)
-- note they don't use recursion on types
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
```
Obviously we don't get any unsoundness from this, since for any `t` built out of `FF` we substitute, we get an intuitionistically true theorem. It's just the general function that may be shocking at first.
##### Inhabitation
Since the types represent classical logic, the problem of inhabitation trivializes a bit. That means that we can find a canonical inhabitant for every type we consider. Functions doing just that are written in `TypeRec.hs`.

### Template integration
Declaring shape and semantics for these types is a bit of repeatable boilerplate, so the file `TemplateTypeRec.hs` implements a function that does it automatically, using TemplateHaskell. It defines an empty datatype `TypeDummy` used to specify the shape of the semantics of each constructor of the datakind. For example the code:
```haskell
$(recursiveTypes [d| 
    data IType = FF Zero | (:->) (TypeDummy -> TypeDummy) | (:+) (Either TypeDummy TypeDummy) | (:*) (TypeDummy, TypeDummy)
        deriving (Eq, Ord, Show)
    |])
```
will produce exactly the definitions used above.

These types can be parametric, further usage is demonstrated in project files. 

### Variadic functions
We will treat the type defined by this signature:
```haskell
$(recursiveTypes [d|
    data IType (a :: *) = FF a | (:->) (TypeDummy -> TypeDummy)
        deriving Show
    |])
```
as a type of variadic functions over some base type `a` represented by `FF`. For example if we want to write a function that, given an unspecified number of integers as arguments, will sum them all up, we can write:
```haskell
sumOfT :: SIType t1 -> GetIType Integer (FF :-> t1)
sumOfT typ = case typ of
    SFF -> \x -> x
    SFF :%-> t2 -> \x y -> sumOfT t2 (x + y)
```
In `TypeRec.hs` we can see that if we use unparametric types, we can write functions that don't require the shape as an argument, and so `sumOf (1 :: Integer) (2 :: Integer) (3 :: Integer) :: Integer` will type correctly and equal to `6`.  
##### Operations on the last argument
In `SwapArgs.hs` we have some type families that help us deal with the last argument. We can extract the shape of the last argument from the shape of the function by using:
```haskell
type family LastArg (t :: IType k) where
    LastArg (t :-> FF) = t
    LastArg (t :-> (ta :-> tb)) = LastArg (ta :-> tb)
```
then we can swap the shape of the last argument for some shape we want by using:
```haskell
type family SwapLastArg (for :: IType k) (t :: IType k) where
    SwapLastArg for FF = FF
    SwapLastArg for (arg :-> FF) = for :-> FF
    SwapLastArg for (arg :-> (ta :-> tb)) = arg :-> (SwapLastArg for (ta :-> tb))
```
Finally we can swap the shapes of the first and last argument of the function with:
```haskell
type family SwapFirstLast (t :: IType k) where
    SwapFirstLast FF = FF
    SwapFirstLast (t :-> FF) = t :-> FF
    SwapFirstLast (t :-> (ta :-> tb)) = (LastArg (ta :-> tb)) :-> (SwapLastArg t (ta :-> tb))
```

Now we have a slightly artificial goal. We want to apply some preprocessing, like negating the value, on the last argument of a variadic `f`. We could do it by induction, but we are close to a tool that helps do it more cleanly: we can swap the first and last argument, then we do the preprocessing on the first, then swap them back. The only problem is that if `f` was of type `t`, we don't get something of type `t` in return, but rather `SwapFirstLast (SwapFirstLast t)`. The rest of the file is dedicated to lemmas that prove these two types are equal:

```haskell
swapLastIdempotent :: SIType t -> SIType ta -> SIType tb -> SwapLastArg (LastArg (ta :-> tb)) (ta :-> tb) :~: ta :-> tb
swapswap :: SIType ta -> SIType tb -> SIType t1 -> SIType t2 -> SwapLastArg t1 (SwapLastArg t2 (ta :-> tb)) :~: SwapLastArg t1 (ta :-> tb)
doubleflip :: SIType t -> SwapFirstLast (SwapFirstLast t) :~: t
```
##### Continuation passing style
This framework can help us rewrite functions to continuation passing style (CPS), in this style:
```haskell
type family CPS (a :: IType k) (t :: IType k) = (r :: IType k) | r -> t where
    CPS a FF = (FF :-> a) :-> a
    CPS a (t :-> t') = ((t :-> a) :-> a) :-> (CPS a t')
```
In the file `CPS.hs` this translation is done with a little bit more generality (for types with function spaces and products), but I can't do it for types with coproducts.

### Heterogenous lists
The framework in itself can only help us write a type for lists with arbitrary (but fixed) nesting:
```haskell
$(recursiveTypes [d|
    data TP a = FF a | HomList [TypeDummy]
        deriving (Eq, Ord, Show)
    |])
```
This has some applications, and can be easily converted to non-nested Haskell lists by a flattening written in `Lists.hs`. However with heterogenous lists we need a type shape that will have a list of all type shapes in the entries of the heterogenous list. We encounter a problem even on the level of singletons. The code:
```haskell
$(singletons [d| 
    data TP' = FF' | HList' [TP']
    |])
```
doesn't compile properly because of how `singletons` deals with constructors. We can however do it manually:

```haskell
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
```
This gives us a way to implement heterogenous lists, with the list constructor being Haskell's regular pair constructor and the empty list being Haskell's unit. For example we have:
```haskell
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
```
We can define a type family for a list with an appended element:
```haskell
type family AppendType (h :: HTP a) (t :: HTP a) :: HTP a where
    AppendType x HFF = HList [x, HFF]
    AppendType x (HList xs) = HList (x:xs)
```
a type family for the concatenation of two lists:
```haskell
type family ConcatType (x :: HTP a) (y :: HTP a) :: HTP a where
    ConcatType HFF (HList ys) = HList (HFF:ys)
    ConcatType (HList '[]) (HList ys) = HList ys
    ConcatType (HList (x:xs)) (HList ys) = AppendType x (ConcatType (HList xs) (HList ys))
    ConcatType a HFF = ConcatType a (HList '[HFF])
```
and finally a type family for the flattening of a list:
```haskell
type family FlattenType (t :: HTP a) :: HTP a where
    FlattenType HFF = HFF
    FlattenType (HList '[]) = HList '[]
    FlattenType (HList (HFF:xs)) = AppendType HFF (FlattenType (HList xs))
    FlattenType (HList ((HList hs):xs)) = ConcatType (FlattenType (HList hs)) (FlattenType (HList xs))
```
Every one of these families (which de facto define the type of the result of some computation) has an associated implementation (of that computation) defined in `Lists.hs`. If we come back to the three hetereogenous lists we defined earlier, we can write:
```haskell
flatlist3 :: GetHTP Integer (HList '[HFF, HFF])
flatlist3 = hflatten slist3 list3
```
and see that indeed `flatlist3` is `(3,(5,()))` as desired. Note: just like in regular functional programming, most functions that type correctly do what is expected of that type, but nothing protects you from writing the type (or in this case type family) wrong.


### Running examples
If you want to effectively test the code in `ghci`, I reccomend running it with:
```bash
ghci -Wincomplete-patterns -fconstraint-solver-iterations=0 -XTemplateHaskell -XStandaloneDeriving -XKindSignatures -XPolyKinds -XDataKinds -XTypeFamilies -XTypeFamilyDependencies -XTypeOperators  -fmax-relevant-binds=10 -ddump-splices -package mtl
```