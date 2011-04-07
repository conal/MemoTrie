{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, ScopedTypeVariables, CPP #-}
{-# OPTIONS_GHC -Wall -fenable-rewrite-rules #-}
-- ScopedTypeVariables works around a 6.10 bug.  The forall keyword is
-- supposed to be recognized in a RULES pragma.

----------------------------------------------------------------------
-- |
-- Module      :  Data.MemoTrie
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Trie-based memoizer
-- Adapted from sjanssen's paste: \"a lazy trie\" <http://hpaste.org/3839>.
----------------------------------------------------------------------

module Data.MemoTrie
  ( HasTrie(..), domain, idTrie, (@.@)
  -- , trie2, trie3, untrie2, untrie3
  , memo, memo2, memo3, mup
  , inTrie, inTrie2, inTrie3
  -- , untrieBits
  ) where

import Data.Bits
import Data.Word
import Data.Int
import Control.Applicative
import Control.Arrow (first,(&&&))
import Data.Monoid
import Data.Function (on)

-- import Prelude hiding (id,(.))
-- import Control.Category
-- import Control.Arrow

infixr 0 :->:

-- | Mapping from all elements of @a@ to the results of some function
class HasTrie a where
    -- | Representation of trie with domain type @a@
    data (:->:) a :: * -> *
    -- | Create the trie for the entire domain of a function
    trie   :: (a  ->  b) -> (a :->: b)
    -- | Convert a trie to a function, i.e., access a field of the trie
    untrie :: (a :->: b) -> (a  ->  b)
    -- | List the trie elements.  Order of keys (@:: a@) is always the same.
    enumerate :: (a :->: b) -> [(a,b)]

-- | Domain elements of a trie
domain :: HasTrie a => [a]
domain = map fst (enumerate (trie (const oops)))
 where
   oops = error "Data.MemoTrie.domain: range element evaluated."

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


{-# RULES
"trie/untrie"   forall t. trie (untrie t) = t
 #-}

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

instance HasTrie () where
    newtype () :->: a = UnitTrie a
    trie f = UnitTrie (f ())
    untrie (UnitTrie a) = \ () -> a
    enumerate (UnitTrie a) = [((),a)]

-- Proofs of inverse properties:

{-
    untrie (trie f)
      == { trie def }
    untrie (UnitTrie (f ()))
      == { untrie def }
    \ () -> (f ())
      == { const-unit }
    f   

    trie (untrie (UnitTrie a))
      == { untrie def }
    trie (\ () -> a)
      == { trie def }
    UnitTrie ((\ () -> a) ())
      == { beta-reduction }
    UnitTrie a

Oops -- the last step of the first direction is bogus when f is non-strict.
Can be fixed by using @const a@ in place of @\ () -> a@, but I can't do
the same for other types, like integers or sums.

All of these proofs have this same bug, unless we restrict ourselves to
memoizing hyper-strict functions.

-}


instance HasTrie Bool where
    data Bool :->: x = BoolTrie x x
    trie f = BoolTrie (f False) (f True)
    untrie (BoolTrie f t) = if' f t
    enumerate (BoolTrie f t) = [(False,f),(True,t)]

-- | Conditional with boolean last.
-- Spec: @if' (f False) (f True) == f@
if' :: x -> x -> Bool -> x
if' t _ False = t
if' _ e True  = e

{-
    untrie (trie f)
      == { trie def }
    untrie (BoolTrie (f False) (f True))
      == { untrie def }
    if' (f False) (f True)
      == { if' spec }
    f

    trie (untrie (BoolTrie f t))
      == { untrie def }
    trie (if' f t)
      == { trie def }
    BoolTrie (if' f t False) (if' f t True)
      == { if' spec }
    BoolTrie f t
-}


instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
    data (Either a b) :->: x = EitherTrie (a :->: x) (b :->: x)
    trie f = EitherTrie (trie (f . Left)) (trie (f . Right))
    untrie (EitherTrie s t) = either (untrie s) (untrie t)
    enumerate (EitherTrie s t) = enum' Left s `weave` enum' Right t

enum' :: (HasTrie a) => (a -> a') -> (a :->: b) -> [(a', b)]
enum' f = (fmap.first) f . enumerate

weave :: [a] -> [a] -> [a]
[] `weave` as = as
as `weave` [] = as
(a:as) `weave` bs = a : (bs `weave` as)

{-
    untrie (trie f)
       == { trie def }
    untrie (EitherTrie (trie (f . Left)) (trie (f . Right)))
       == { untrie def }
    either (untrie (trie (f . Left))) (untrie (trie (f . Right)))
       == { untrie . trie }
    either (f . Left) (f . Right)
       == { either }
    f

    trie (untrie (EitherTrie s t))
       == { untrie def }
    trie (either (untrie s) (untrie t))
       == { trie def }
    EitherTrie (trie (either (untrie s) (untrie t) . Left))
               (trie (either (untrie s) (untrie t) . Right))
       == { either }
    EitherTrie (trie (untrie s)) (trie (untrie t))
       == { trie . untrie }
    EitherTrie s t
-}


instance (HasTrie a, HasTrie b) => HasTrie (a,b) where
    newtype (a,b) :->: x = PairTrie (a :->: (b :->: x))
    trie f = PairTrie (trie (trie . curry f))
    untrie (PairTrie t) = uncurry (untrie .  untrie t)
    enumerate (PairTrie tt) =
      [ ((a,b),x) | (a,t) <- enumerate tt , (b,x) <- enumerate t ]

{-
    untrie (trie f)
      == { trie def }
    untrie (PairTrie (trie (trie . curry f)))
      == { untrie def }
    uncurry (untrie . untrie (trie (trie . curry f)))
      == { untrie . trie }
    uncurry (untrie . trie . curry f)
      == { untrie . untrie }
    uncurry (curry f)
      == { uncurry . curry }
    f

    trie (untrie (PairTrie t))
      == { untrie def }
    trie (uncurry (untrie .  untrie t))
      == { trie def }
    PairTrie (trie (trie . curry (uncurry (untrie .  untrie t))))
      == { curry . uncurry }
    PairTrie (trie (trie . untrie .  untrie t))
      == { trie . untrie }
    PairTrie (trie (untrie t))
      == { trie . untrie }
    PairTrie t
-}

instance (HasTrie a, HasTrie b, HasTrie c) => HasTrie (a,b,c) where
    newtype (a,b,c) :->: x = TripleTrie (((a,b),c) :->: x)
    trie f = TripleTrie (trie (f . trip))
    untrie (TripleTrie t) = untrie t . detrip
    enumerate (TripleTrie t) = enum' trip t

trip :: ((a,b),c) -> (a,b,c)
trip ((a,b),c) = (a,b,c)

detrip :: (a,b,c) -> ((a,b),c)
detrip (a,b,c) = ((a,b),c)


instance HasTrie x => HasTrie [x] where
    newtype [x] :->: a = ListTrie (Either () (x,[x]) :->: a)
    trie f = ListTrie (trie (f . list))
    untrie (ListTrie t) = untrie t . delist
    enumerate (ListTrie t) = enum' list t

list :: Either () (x,[x]) -> [x]
list = either (const []) (uncurry (:))

delist :: [x] -> Either () (x,[x])
delist []     = Left ()
delist (x:xs) = Right (x,xs)

#define WordInstance(Type,TrieType)\
instance HasTrie Type where \
    newtype Type :->: a = TrieType ([Bool] :->: a);\
    trie f = TrieType (trie (f . unbits));\
    untrie (TrieType t) = untrie t . bits;\
    enumerate (TrieType t) = enum' unbits t

WordInstance(Word,WordTrie)
WordInstance(Word8,Word8Trie)
WordInstance(Word16,Word16Trie)
WordInstance(Word32,Word32Trie)
WordInstance(Word64,Word64Trie)

-- instance HasTrie Word where
--     newtype Word :->: a = WordTrie ([Bool] :->: a)
--     trie f = WordTrie (trie (f . unbits))
--     untrie (WordTrie t) = untrie t . bits
--     enumerate (WordTrie t) = enum' unbits t


-- | Extract bits in little-endian order
bits :: Bits t => t -> [Bool]
bits 0 = []
bits x = testBit x 0 : bits (shiftR x 1)

-- | Convert boolean to 0 (False) or 1 (True)
unbit :: Num t => Bool -> t
unbit False = 0
unbit True  = 1

-- | Bit list to value
unbits :: Bits t => [Bool] -> t
unbits [] = 0
unbits (x:xs) = unbit x .|. shiftL (unbits xs) 1

instance HasTrie Char where
    newtype Char :->: a = CharTrie (Int :->: a)
    untrie (CharTrie t) n = untrie t (fromEnum n)
    trie f = CharTrie (trie (f . toEnum))
    enumerate (CharTrie t) = enum' toEnum t

-- Although Int is a Bits instance, we can't use bits directly for
-- memoizing, because the "bits" function gives an infinite result, since
-- shiftR (-1) 1 == -1.  Instead, convert between Int and Word, and use
-- a Word trie.  Any Integral type can be handled similarly.

#define IntInstance(IntType,WordType,TrieType) \
instance HasTrie IntType where \
    newtype IntType :->: a = TrieType (WordType :->: a); \
    untrie (TrieType t) n = untrie t (fromIntegral n); \
    trie f = TrieType (trie (f . fromIntegral)); \
    enumerate (TrieType t) = enum' fromIntegral t

IntInstance(Int,Word,IntTrie)
IntInstance(Int8,Word8,Int8Trie)
IntInstance(Int16,Word16,Int16Trie)
IntInstance(Int32,Word32,Int32Trie)
IntInstance(Int64,Word64,Int64Trie)

-- For unbounded integers, we don't have a corresponding Word type, so
-- extract the sign bit.

instance HasTrie Integer where
    newtype Integer :->: a = IntegerTrie ((Bool,[Bool]) :->: a)
    trie f = IntegerTrie (trie (f . unbitsZ))
    untrie (IntegerTrie t) = untrie t . bitsZ
    enumerate (IntegerTrie t) = enum' unbitsZ t


unbitsZ :: (Bits n) => (Bool,[Bool]) -> n
unbitsZ (positive,bs) = sig (unbits bs)
 where
   sig | positive  = id
       | otherwise = negate

bitsZ :: (Ord n, Bits n) => n -> (Bool,[Bool])
bitsZ = (>= 0) &&& (bits . abs)

-- bitsZ n = (sign n, bits (abs n))



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
