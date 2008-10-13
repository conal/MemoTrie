{-# LANGUAGE GADTs, TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -Wall -frewrite-rules #-}
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
-- Adapted from sjanssen's paste: "a lazy trie" <http://hpaste.org/3839>.
----------------------------------------------------------------------

module Data.MemoTrie
  ( HasTrie(..)
  , memo, memo2, memo3, mup
  , trieBits, untrieBits
  ) where

import Data.Bits
import Data.Word
import Control.Applicative
import Data.Monoid

-- | Mapping from all elements of @a@ to the results of some function
class HasTrie a where
    -- | Representation of trie with domain type @a@
    data (:->:) a :: * -> *
    -- Create the trie for the entire domain of a function
    trie   :: (a  ->  b) -> (a :->: b)
    -- | Convert a trie to a function, i.e., access a field of the trie
    untrie :: (a :->: b) -> (a  ->  b)

{-# RULES
"trie/untrie"   forall t. trie (untrie t) = t
"untrie/trie"   forall f. untrie (trie f) = f
 #-}

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


---- Instances

instance HasTrie () where
    data () :->: a = UnitTrie a
    trie f = UnitTrie (f ())
    untrie (UnitTrie x) () = x

instance HasTrie Bool where
    data Bool :->: a = BoolTrie a a
    trie f = BoolTrie (f False) (f True)
    untrie (BoolTrie f _) False = f
    untrie (BoolTrie _ t) True  = t

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
    data (Either a b) :->: x = EitherTrie (a :->: x) (b :->: x)
    untrie (EitherTrie f _) (Left  x) = untrie f x
    untrie (EitherTrie _ g) (Right y) = untrie g y
    trie f = EitherTrie (trie (f . Left)) (trie (f . Right))

instance (HasTrie a, HasTrie b) => HasTrie (a,b) where
    data (a,b) :->: x = PairTrie (a :->: (b :->: x))
    untrie (PairTrie f) (a,b) = untrie (untrie f a) b
    trie f = PairTrie $ trie $ \a -> trie $ \b -> f (a,b)

instance (HasTrie a, HasTrie b, HasTrie c) => HasTrie (a,b,c) where
    data (a,b,c) :->: x = TripleTrie (a :->: (b :->: (c :->: x)))
    untrie (TripleTrie f) (a,b,c) = untrie (untrie (untrie f a) b) c
    trie f = TripleTrie $
      trie $ \a -> trie $ \b -> trie $ \ c -> f (a,b,c)

instance HasTrie x => HasTrie [x] where
    data [x] :->: a = ListTrie a (x :->: ([x] :->: a))
    trie f = ListTrie (f []) $ trie (\x -> trie (f . (x:)))
    untrie (ListTrie n _) []     = n
    untrie (ListTrie _ t) (x:xs) = untrie (untrie t x) xs

-- TODO: make these definitions more systematic.


-- Handy for Bits types

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

-- | Handy for 'trie' in a bits-based 'Trie' instance
trieBits :: Bits t => (t -> a) -> ([Bool] :->: a)
trieBits f = trie (f . unbits)

-- | Handy for 'untrie' in a bits-based 'Trie' instance
untrieBits :: Bits t => ([Bool] :->: a) -> (t -> a)
untrieBits t x = untrie t (bits x)

instance HasTrie Word where
    data Word :->: a = WordTrie ([Bool] :->: a)
    untrie (WordTrie t) = untrieBits t
    trie = WordTrie . trieBits

-- Although Int is a Bits instance, we can't use bits directly for
-- memoizing, because the "bits" function gives an infinite result, since
-- shiftR (-1) 1 == -1.  Instead, convert between Int and Word, and use
-- a Word trie.

instance HasTrie Int where
    data Int :->: a = IntTrie (Word :->: a)
    untrie (IntTrie t) n = untrie t (fromIntegral n)
    trie f = IntTrie (trie (f . fromIntegral . toInteger))


---- Instances

{-

The \"semantic function\" 'untrie' is a morphism over 'Monoid', 'Functor',
'Applicative', and 'Monad', i.e.,

  untrie mempty          == mempty
  untrie (s `mappend` t) == untrie s `mappend` untrie t

  untrie (fmap f t)      == fmap f (untrie t)

  untrie (pure a)        == pure a
  untrie (tf <*> tx)     == untrie tf <*> untrie tx

  untrie (return a)      == return a
  untrie (u >>= k)       == untrie u >>= untrie . k

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

Correctness of these instances follows by applying 'untrie' to each side
of each definition and using the property @'untrie' . 'trie' == 'id'@.

-}

instance (HasTrie a, Monoid b) => Monoid (a :->: b) where
  mempty        = trie mempty
  s `mappend` t = trie (untrie s `mappend` untrie t)

instance HasTrie a => Functor ((:->:) a) where
  fmap f t      = trie (fmap f (untrie t))

instance HasTrie a => Applicative ((:->:) a) where
  pure b        = trie (pure b)
  tf <*> tx     = trie (untrie tf <*> untrie tx)

instance HasTrie a => Monad ((:->:) a) where
  return a      = trie (return a)
  u >>= k       = trie (untrie u >>= untrie . k)
