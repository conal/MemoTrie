{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, ScopedTypeVariables, CPP #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures, FlexibleContexts, LambdaCase, DeriveGeneric #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 708)
{-# LANGUAGE EmptyCase #-}
#endif
{-# OPTIONS_GHC -Wall -fenable-rewrite-rules #-}

-- ScopedTypeVariables works around a 6.10 bug.  The forall keyword is
-- supposed to be recognized in a RULES pragma.

----------------------------------------------------------------------
-- |
-- Module      :  Data.MemoTrie
-- Copyright   :  (c) Conal Elliott 2008-2016
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Trie-based memoizer
-- 
-- Adapted from sjanssen's paste: <http://hpaste.org/3839 \"a lazy trie\">,
-- which I think is based on Ralf Hinze's paper "Memo Functions,
-- Polytypically!".
-- 
-- You can automatically derive generic instances. for example: 
-- 
-- @
-- {-# LANGUAGE <https://ocharles.org.uk/blog/posts/2014-12-16-derive-generic.html DeriveGeneric>, TypeOperators, TypeFamilies #-}
-- import Data.MemoTrie
-- import GHC.Generics (Generic) 
-- 
-- data Color = RGB Int Int Int
--            | NamedColor String 
--  deriving ('Generic') 
-- 
-- instance HasTrie Color
-- @
-- 
-- see @examples/Generic.hs@, which can be run with: 
-- 
-- @
-- cabal configure -fexamples && cabal run generic
-- @ 
-- 
-- 
----------------------------------------------------------------------

module Data.MemoTrie
  ( HasTrie(..), (:->:)(..)
  , trie, untrie, enumerate
  , domain, idTrie, (@.@)
  -- , trie2, trie3, untrie2, untrie3
  , memo, memo2, memo3, mup
  , inTrie, inTrie2, inTrie3
  -- , untrieBits
  , memoFix
  ) where

-- Export the parts of HasTrie separately in order to get the associated data
-- type constructors, so I can define instances of other classes on them.

import Data.Function (fix)
import Data.Bits
import Data.Word
import Data.Int
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Arrow (first,(&&&))
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif
import Data.Function (on)
import GHC.Generics

import Data.Void (Void) 
 
-- import Prelude hiding (id,(.))
-- import Control.Category
-- import Control.Arrow

infixr 0 :->:, :->, :->>
newtype (:->:) a b = Trie {getTrie :: a :-> b} deriving (Generic)

-- | Mapping from all elements of @a@ to the results of some function
class HasTrie a where
    -- | Representation of trie with domain type @a@
    type (:->) a b :: *
    type (:->) a b = Rep a :->> b
    -- | Create the trie for the entire domain of a function
    trie'   :: (a  ->  b) -> (a :-> b)
    default trie' :: (Generic a, GHasTrie (Rep a), (a :-> b) ~ (Rep a :->> b))
                  => (a -> b) -> (a :-> b)
    trie' f = trie'' (f . (to :: Rep a () -> a))
    -- | Convert a trie to a function, i.e., access a field of the trie
    untrie' :: (a :-> b) -> (a  ->  b)
    default untrie' :: (Generic a, GHasTrie (Rep a), (a :-> b) ~ (Rep a :->> b))
                    => (a :-> b) -> (a -> b)
    untrie' q = untrie'' q . (from :: a -> Rep a ())
    -- | List the trie elements.  Order of keys (@:: a@) is always the same.
    enumerate' :: (a :-> b) -> [(a,b)]
    default enumerate' :: (Generic a, GHasTrie (Rep a), (a :-> b) ~ (Rep a :->> b))
                       => (a :-> b) -> [(a,b)]
    enumerate' = map (first (to :: Rep a () -> a)) . enumerate''

class GHasTrie f where
    -- | Representation of trie with domain type @a@
    data (:->>) (f :: * -> *) :: * -> *
    -- | Create the trie for the entire domain of a function
    trie''   :: (f a -> b) -> (f :->> b)
    -- | Convert a trie to a function, i.e., access a field of the trie
    untrie'' :: (f :->> b) -> (f a -> b)
    -- | List the trie elements.  Order of keys (@:: a@) is always the same.
    enumerate'' :: (f :->> b) -> [(f a,b)]

-- | Create the trie for the entire domain of a function
trie   :: HasTrie a => (a -> b) -> (a :->: b)
trie = Trie . trie'
-- | Convert a trie to a function, i.e., access a field of the trie
untrie :: HasTrie a => (a :->: b) -> (a  ->  b)
untrie = untrie' . getTrie
-- | List the trie elements.  Order of keys (@:: a@) is always the same.
enumerate :: HasTrie a => (a :->: b) -> [(a,b)]
enumerate = enumerate' . getTrie

-- | Domain elements of a trie
domain :: HasTrie a => [a]
domain = map fst (enumerate (trie (const ())))

-- Hm: domain :: [Bool] doesn't produce any output.

instance (HasTrie a, Eq b) => Eq (a :->: b) where
  (==) = (==) `on` (map snd . enumerate)

instance (HasTrie a, Show a, Show b) => Show (a :->: b) where
  show t = "Trie: " ++ show (enumerate t)

{-
trie2 :: (HasTrie a, HasTrie b) =>
         (a -> b -> c) -> (a :->: b :->: c)
-- trie2 h = trie $ \ a -> trie $ \ b -> h a b
-- trie2 h = trie $ \ a -> trie (h a)
trie2 h = trie (trie . h)
-- trie2 h = trie (fmap trie h)
-- trie2 = (fmap.fmap) trie trie


trie3 :: (HasTrie a, HasTrie b, HasTrie c) =>
         (a -> b -> c -> d) -> (a :->: b :->: c :->: d)
trie3 h = trie (trie2 . h)

untrie2 :: (HasTrie a, HasTrie b) =>
          (a :->: b :->: c)-> (a -> b -> c)
untrie2 tt = untrie . untrie tt


untrie3 :: (HasTrie a, HasTrie b, HasTrie c) =>
          (a :->: b :->: c :->: d)-> (a -> b -> c -> d)
untrie3 tt = untrie2 . untrie tt
-}


-- {-# RULES "trie/untrie"   forall t. trie (untrie t) = t #-}

--     warning: [-Winline-rule-shadowing] …
--     Rule "trie/untrie" may never fire
--       because rule "Class op untrie" for ‘untrie’ might fire first
--     Probable fix: add phase [n] or [~n] to the competing rule


-- Don't include the dual rule:
--   "untrie/trie"   forall f. untrie (trie f) = f
-- which would defeat memoization.
--
-- TODO: experiment with rule application.  Maybe re-enable "untrie/trie"
-- but fiddle with phases, so it won't defeat 'memo'.

-- | Trie-based function memoizer
memo :: HasTrie t => (t -> a) -> (t -> a)
memo = untrie . trie

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: (HasTrie s,HasTrie t) => (s -> t -> a) -> (s -> t -> a)

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: (HasTrie r,HasTrie s,HasTrie t) => (r -> s -> t -> a) -> (r -> s -> t -> a)

-- | Lift a memoizer to work with one more argument.
mup :: HasTrie t => (b -> c) -> (t -> b) -> (t -> c)
mup mem f = memo (mem . f)

memo2 = mup memo
memo3 = mup memo2

-- | Memoizing recursion. Use like `fix`.
memoFix :: HasTrie a => ((a -> b) -> (a -> b)) -> (a -> b)
memoFix h = fix (memo . h)

#if 0
-- Equivalently,

memoFix h = fix (\ f' -> memo (h f'))

memoFix h = f'
  where f' = memo (h f')

memoFix h = f'
 where
   f' = memo f
   f  = h f'
#endif

#if 0
-- Example

fibF :: (Integer -> Integer) -> (Integer -> Integer)
fibF _ 0 = 1
fibF _ 1 = 1
fibF f n = f (n-1) + f (n-2)

fib :: Integer -> Integer
fib = fix fibF

fib' :: Integer -> Integer
fib' = memoFix fibF

-- Try fib 30 vs fib' 30
#endif

-- | Apply a unary function inside of a trie
inTrie :: (HasTrie a, HasTrie c) =>
          ((a  ->  b) -> (c  ->  d))
       -> ((a :->: b) -> (c :->: d))
inTrie = untrie ~> trie

-- | Apply a binary function inside of a trie
inTrie2 :: (HasTrie a, HasTrie c, HasTrie e) =>
           ((a  ->  b) -> (c  ->  d) -> (e  ->  f))
        -> ((a :->: b) -> (c :->: d) -> (e :->: f))
inTrie2 = untrie ~> inTrie

-- | Apply a ternary function inside of a trie
inTrie3 :: (HasTrie a, HasTrie c, HasTrie e, HasTrie g) =>
           ((a  ->  b) -> (c  ->  d) -> (e  ->  f) -> (g  ->  h))
        -> ((a :->: b) -> (c :->: d) -> (e :->: f) -> (g :->: h))
inTrie3 = untrie ~> inTrie2


---- Instances

instance HasTrie Void
instance HasTrie ()
instance HasTrie Bool
instance (HasTrie a, HasTrie b) => HasTrie (Either a b)
instance (HasTrie a, HasTrie b) => HasTrie (a,b)
instance (HasTrie a, HasTrie b, HasTrie c) => HasTrie (a,b,c)
instance (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => HasTrie (a,b,c,d)
instance (HasTrie a, HasTrie b, HasTrie c, HasTrie d, HasTrie e) => HasTrie (a,b,c,d,e)
instance HasTrie x => HasTrie [x]
instance HasTrie (a :-> b) => HasTrie (a :->: b)

#define WordInstance(Type)\
instance HasTrie Type where \
  type Type :-> a = ([Bool] :-> a);\
  trie' f = trie' (f . unbits);\
  untrie' t = untrie' t . bits;\
  enumerate' t = enum' unbits t

WordInstance(Word)
WordInstance(Word8)
WordInstance(Word16)
WordInstance(Word32)
WordInstance(Word64)

-- instance HasTrie Word where
--   newtype Word :->: a = WordTrie ([Bool] :->: a)
--   trie f = WordTrie (trie (f . unbits))
--   untrie (WordTrie t) = untrie t . bits
--   enumerate (WordTrie t) = enum' unbits t


-- | Extract bits in little-endian order
bits :: (Num t, Bits t) => t -> [Bool]
bits 0 = []
bits x = testBit x 0 : bits (shiftR x 1)

-- | Convert boolean to 0 (False) or 1 (True)
unbit :: Num t => Bool -> t
unbit False = 0
unbit True  = 1

-- | Bit list to value
unbits :: (Num t, Bits t) => [Bool] -> t
unbits [] = 0
unbits (x:xs) = unbit x .|. shiftL (unbits xs) 1

instance HasTrie Char where
  type Char :-> a = Int :-> a
  untrie' t n = untrie' t (fromEnum n)
  trie' f = trie' (f . toEnum)
  enumerate' t = enum' toEnum t

-- Although Int is a Bits instance, we can't use bits directly for
-- memoizing, because the "bits" function gives an infinite result, since
-- shiftR (-1) 1 == -1.  Instead, convert between Int and Word, and use
-- a Word trie.  Any Integral type can be handled similarly.

#define IntInstance(IntType,WordType) \
instance HasTrie IntType where \
  type IntType :-> a = WordType :-> a;\
  untrie' t n = untrie' t (fromIntegral n :: WordType); \
  trie' f = trie' (f . (fromIntegral :: WordType -> IntType)); \
  enumerate' t = enum' (fromIntegral :: WordType -> IntType) t

IntInstance(Int,Word)
IntInstance(Int8,Word8)
IntInstance(Int16,Word16)
IntInstance(Int32,Word32)
IntInstance(Int64,Word64)

-- For unbounded integers, we don't have a corresponding Word type, so
-- extract the sign bit.

instance HasTrie Integer where
  type Integer :-> a = (Bool,[Bool]) :-> a
  trie' f = trie' (f . unbitsZ)
  untrie' t = untrie' t . bitsZ
  enumerate' t = enum' unbitsZ t

unbitsZ :: (Num n, Bits n) => (Bool,[Bool]) -> n
unbitsZ (positive,bs) = sig (unbits bs)
 where
   sig | positive  = id
       | otherwise = negate

bitsZ :: (Num n, Ord n, Bits n) => n -> (Bool,[Bool])
bitsZ = (>= 0) &&& (bits . abs)

-- TODO: make these definitions more systematic.

---- Instances

{-

The \"semantic function\" 'untrie' is a morphism over 'Monoid', 'Functor',
'Applicative', 'Monad', 'Category', and 'Arrow', i.e.,

  untrie mempty          == mempty
  untrie (s `mappend` t) == untrie s `mappend` untrie t

  untrie (fmap f t)      == fmap f (untrie t)

  untrie (pure a)        == pure a
  untrie (tf <*> tx)     == untrie tf <*> untrie tx

  untrie (return a)      == return a
  untrie (u >>= k)       == untrie u >>= untrie . k

  untrie id              == id
  untrie (s . t)         == untrie s . untrie t

  untrie (arr f)         == arr f
  untrie (first t)       == first (untrie t)

These morphism properties imply that all of the expected laws hold,
assuming that we interpret equality semantically (or observationally).
For instance,

  untrie (mempty `mappend` a)
    == untrie mempty `mappend` untrie a
    == mempty `mappend` untrie a
    == untrie a

  untrie (fmap f (fmap g a))
    == fmap f (untrie (fmap g a))
    == fmap f (fmap g (untrie a))
    == fmap (f.g) (untrie a)
    == untrie (fmap (f.g) a)

The implementation instances then follow from applying 'trie' to both
sides of each of these morphism laws.

-}

{-
instance (HasTrie a, Monoid b) => Monoid (a :->: b) where
  mempty  = trie mempty
  s `mappend` t = trie (untrie s `mappend` untrie t)

instance HasTrie a => Functor ((:->:) a) where
  fmap f t      = trie (fmap f (untrie t))

instance HasTrie a => Applicative ((:->:) a) where
  pure b        = trie (pure b)
  tf <*> tx     = trie (untrie tf <*> untrie tx)

instance HasTrie a => Monad ((:->:) a) where
  return a      = trie (return a)
  u >>= k       = trie (untrie u >>= untrie . k)

-- instance Category (:->:) where
--   id            = trie id
--   s . t         = trie (untrie s . untrie t)

-- instance Arrow (:->:) where
--   arr f         = trie (arr f)
--   first t       = trie (first (untrie t))
-}

-- Simplify, using inTrie, inTrie2

instance (HasTrie a, Monoid b) => Monoid (a :->: b) where
  mempty  = trie mempty
  mappend = inTrie2 mappend

instance HasTrie a => Functor ((:->:) a) where
  fmap f = inTrie (fmap f)

instance HasTrie a => Applicative ((:->:) a) where
  pure b = trie (pure b)
  (<*>)  = inTrie2 (<*>)

instance HasTrie a => Monad ((:->:) a) where
  return a = trie (return a)
  u >>= k  = trie (untrie u >>= untrie . k)

-- | Identity trie
idTrie :: HasTrie a => a :->: a
idTrie = trie id

infixr 9 @.@
-- | Trie composition
(@.@) :: (HasTrie a, HasTrie b) =>
         (b :->: c) -> (a :->: b) -> (a :->: c)
(@.@) = inTrie2 (.)


-- instance Category (:->:) where
--   id  = idTrie
--   (.) = (.:)

-- instance Arrow (:->:) where
--   arr f = trie (arr f)
--   first = inTrie first

{-

Correctness of these instances follows by applying 'untrie' to each side
of each definition and using the property @'untrie' . 'trie' == 'id'@.

The `Category` and `Arrow` instances don't quite work, however, because of
necessary but disallowed `HasTrie` constraints on the domain type.

-}

---- To go elsewhere

-- Matt Hellige's notation for @argument f . result g@.
-- <http://matt.immute.net/content/pointless-fun>


(~>) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
g ~> f = (f .) . (. g)


{-
-- Examples
f1,f1' :: Int -> Int
f1 n = n + n

f1' = memo f1
-}

-- We INLINE all the generic implementations in the hope that
-- GHC will produce instances like the ones we would write
-- by hand. We need to use a data family here to prevent the
-- type checker from looping on recursive types.

-- | just like @void@ 
instance GHasTrie V1 where
  data V1 :->> b = V1Trie
  trie'' _ = V1Trie
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 708)
  untrie'' V1Trie = \ x -> case x of
#else
  untrie'' V1Trie = \ x -> x `seq` error "untrie V1Trie"
#endif
  enumerate'' V1Trie = [] 
  {-# INLINE trie'' #-}
  {-# INLINE untrie'' #-}
  {-# INLINE enumerate'' #-}

-- | just like @()@ 
instance GHasTrie U1 where
  data U1 :->> b = U1Trie b
  trie'' f = U1Trie $ f U1
  untrie'' (U1Trie b) = \U1 -> b
  enumerate'' (U1Trie b) = [(U1, b)] 
  {-# INLINE trie'' #-}
  {-# INLINE untrie'' #-}
  {-# INLINE enumerate'' #-}

-- Proofs of inverse properties:

{-
    untrie (trie f)
      == { trie def }
    untrie (U1Trie (f U1))
      == { untrie def }
    \ U1 -> (f U1)
      == { const-unit }
    f   

    trie (untrie (U1Trie a))
      == { untrie def }
    trie (\ U1 -> a)
      == { trie def }
    U1Trie ((\ U1 -> a) ())
      == { beta-reduction }
    U1Trie a

Oops -- the last step of the first direction is bogus when f is non-strict.
Can be fixed by using @const a@ in place of @\ U1 -> a@, but I can't do
the same for other types, like integers or sums.

All of these proofs have this same bug, unless we restrict ourselves to
memoizing hyper-strict functions.

-}

instance (GHasTrie f, GHasTrie g) => GHasTrie (f :+: g) where
  data (f :+: g) :->> b = EitherTrie (f :->> b) (g :->> b)
  trie'' f = EitherTrie (trie'' (f . L1)) (trie'' (f . R1))
  untrie'' (EitherTrie f _g) (L1 l) = untrie'' f l
  untrie'' (EitherTrie _f g) (R1 r) = untrie'' g r
  enumerate'' (EitherTrie s t) = enum'' L1 s `weave` enum'' R1 t
  {-# INLINE trie'' #-}
  {-# INLINE untrie'' #-}
  {-# INLINE enumerate'' #-}

enum' :: HasTrie a => (a -> a') -> (a :-> b) -> [(a', b)]
enum' f = (fmap.first) f . enumerate'

enum'' :: GHasTrie f => (f a -> g a) -> (f :->> b) -> [(g a, b)]
enum'' f = (fmap.first) f . enumerate''

weave :: [a] -> [a] -> [a]
[] `weave` as = as
as `weave` [] = as
(a:as) `weave` bs = a : (bs `weave` as)


{-
    untrie (trie f)
       == { trie def }
    untrie (EitherTrie (trie (f . L1)) (trie (f . R1)))
       == { untrie def }
    either (untrie (trie (f . L1))) (untrie (trie (f . R1)))
       == { untrie . trie }
    either (f . L1) (f . R1)
       == { either }
    f

    trie (untrie (EitherTrie s t))
       == { untrie def }
    trie (either (untrie s) (untrie t))
       == { trie def }
    EitherTrie (trie (either (untrie s) (untrie t) . L1))
               (trie (either (untrie s) (untrie t) . R1))
       == { either }
    EitherTrie (trie (untrie s)) (trie (untrie t))
       == { trie . untrie }
    EitherTrie s t
-}



instance (GHasTrie f, GHasTrie g) => GHasTrie (f :*: g) where
  data (f :*: g) :->> b = ProductTrie (f :->> g :->> b)
  trie'' f = ProductTrie $ trie'' (\x -> trie'' (\y -> f (x :*: y)))
  untrie'' (ProductTrie t) = \(x :*: y) -> (untrie'' . untrie'' t) x y
  enumerate'' (ProductTrie tt) = [((a :*: b), x) | (a, t) <- enumerate'' tt, (b, x) <- enumerate'' t]
  {-# INLINE trie'' #-}
  {-# INLINE untrie'' #-}
  {-# INLINE enumerate'' #-}

{-
    -- Let curryP and uncurryP curry and uncurry :*:
    untrie (trie f)
      == { trie def }
    untrie (ProductTrie (trie (trie . curryP f)))
      == { untrie def }
    uncurryP (untrie . untrie (trie (trie . curryP f)))
      == { untrie . trie }
    uncurryP (untrie . trie . curryP f)
      == { untrie . untrie }
    uncurryP (curryP f)
      == { uncurryP . curryP }
    f

    trie (untrie (ProductTrie t))
      == { untrie def }
    trie (uncurryP (untrie .  untrie t))
      == { trie def }
    ProductTrie (trie (trie . curryP (uncurryP (untrie .  untrie t))))
      == { curryP . uncurryP }
    ProductTrie (trie (trie . untrie .  untrie t))
      == { trie . untrie }
    ProductTrie (trie (untrie t))
      == { trie . untrie }
    ProductTrie t
-}


instance HasTrie a => GHasTrie (K1 i a) where
  data K1 i a :->> b = K1Trie (a :-> b)
  trie'' f = K1Trie $ trie' (f . K1)
  untrie'' (K1Trie t) = \(K1 a) -> (untrie' t) a 
  enumerate'' (K1Trie t) = enum' K1 t
  {-# INLINE trie'' #-}
  {-# INLINE untrie'' #-}
  {-# INLINE enumerate'' #-}

instance GHasTrie f => GHasTrie (M1 i t f) where
  data M1 i t f :->> b = M1Trie (f :->> b)
  trie'' f = M1Trie $ trie'' (f . M1)
  untrie'' (M1Trie t) = \(M1 a) -> (untrie'' t) a  
  enumerate'' (M1Trie t) = enum'' M1 t 
  {-# INLINE trie'' #-}
  {-# INLINE untrie'' #-}
  {-# INLINE enumerate'' #-}
