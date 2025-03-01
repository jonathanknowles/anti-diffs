{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}

-- | See the module documentation for "Data.Map.Diff.Strict".
module Data.Map.Diff.Strict.Internal (
    -- * Types
    Delta (..)
  , DeltaHistory (..)
  , Diff (..)
    -- * Conversion
  , keysSet
    -- * Construction
  , diff
  , empty
    -- ** Maps
  , fromMap
  , fromMapDeletes
  , fromMapInserts
    -- ** Lists
  , fromList
  , fromListDeletes
  , fromListDeltaHistories
  , fromListInserts
    -- ** Delta history
  , singleton
  , singletonDelete
  , singletonInsert
    -- * Deconstruction
    -- ** Delta history
  , last
    -- * Query
    -- ** Size
  , null
  , numDeletes
  , numInserts
  , size
    -- * Applying diffs
  , applyDiff
  , applyDiffForKeys
    -- * Folds and traversals
  , foldMapDelta
  , mapMaybeDiff
  , traverseDeltaWithKey_
    -- * Filter
  , filterOnlyKey
  ) where

import           Control.Monad (void)
import           Data.Bifunctor (Bifunctor (second))
import           Data.Foldable (foldMap', toList)
import qualified Data.Map.Merge.Strict as Merge
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import           Data.Monoid (Sum (..))
import           Data.MonoidMap (MonoidMap)
import qualified Data.MonoidMap as MonoidMap
import           Data.Semigroup.Cancellative (LeftCancellative,
                     LeftReductive (..), RightCancellative, RightReductive (..))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Sequence.NonEmpty (NESeq (..))
import qualified Data.Sequence.NonEmpty as NESeq
import           Data.Sequence.NonEmpty.Extra ()
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import           NoThunks.Class (NoThunks (..))
import           Prelude hiding (last, length, null, splitAt)

{------------------------------------------------------------------------------
  Types
------------------------------------------------------------------------------}

-- | A diff for key-value stores.
newtype Diff k v = Diff (MonoidMap k (Seq (Delta v)))
  deriving stock (Generic, Show, Eq)
  deriving anyclass (NoThunks)
  deriving newtype
    ( Semigroup
    , Monoid
    , LeftCancellative
    , LeftReductive
    , RightCancellative
    , RightReductive
    )

-- | Custom 'Functor' instance, since @'Functor' ('Map' k)@ is actually the
-- 'Functor' instance for a lazy Map.
instance Functor (Diff k) where
  fmap f (Diff m) = Diff $ MonoidMap.map (fmap (fmap f)) m

-- | A non-empty history of changes to a value in a key-value store.
--
-- A history has an implicit sense of ordering according to time: from left to
-- right. This means that the leftmost element in the history is the /earliest/
-- change, while the rightmost element in the history is the /latest/ change.
newtype DeltaHistory v = DeltaHistory { getDeltaHistory :: NESeq (Delta v) }
  deriving stock (Generic, Show, Eq, Functor)
  deriving newtype (NoThunks, Semigroup)

-- | A change to a value in a key-value store.
data Delta v =
      Insert !v
    | Delete
  deriving stock (Generic, Show, Eq, Functor, Foldable, Traversable)
  deriving anyclass (NoThunks)

{------------------------------------------------------------------------------
  Conversion
------------------------------------------------------------------------------}

keysSet :: Diff k v -> Set k
keysSet (Diff m) = MonoidMap.nonNullKeys m

{------------------------------------------------------------------------------
  Construction
------------------------------------------------------------------------------}

-- | Compute the difference between @'Map'@s.
diff :: (Ord k, Eq v) => Map k v -> Map k v -> Diff k v
diff m1 m2 = Diff $
    MonoidMap.fromMap $
    Merge.merge
      (Merge.mapMissing $ \_k _v -> Seq.singleton Delete)
      (Merge.mapMissing $ \_k v -> Seq.singleton (Insert v))
      (Merge.zipWithMaybeMatched $ \ _k v1 v2 ->
        if v1 == v2 then
          Nothing
        else
          Just $ Seq.singleton Delete <> Seq.singleton (Insert v2)
      )
      m1
      m2

empty :: Diff k v
empty = Diff MonoidMap.empty

-- | @'fromMap' m@ creates a @'Diff'@ from the inserts and deletes in @m@.
fromMap :: Map k (Delta v) -> Diff k v
fromMap = Diff . MonoidMap.fromMapWith Seq.singleton

-- | @'fromMapInserts' m@ creates a @'Diff'@ that inserts all values in @m@.
fromMapInserts :: Map k v -> Diff k v
fromMapInserts = Diff . MonoidMap.fromMapWith (Seq.singleton . Insert)

-- | @'fromMapDeletes' m@ creates a @'Diff'@ that deletes all values in @m@.
fromMapDeletes :: Map k v -> Diff k v
fromMapDeletes = Diff . MonoidMap.fromMapWith (const $ Seq.singleton Delete)

fromListDeltaHistories :: Ord k => [(k, DeltaHistory v)] -> Diff k v
fromListDeltaHistories =
  Diff . MonoidMap.fromList . fmap (fmap (NESeq.toSeq . getDeltaHistory))

-- | @'fromList' xs@ creates a @'Diff'@ from the inserts and deletes in @xs@.
fromList :: Ord k => [(k, Delta v)] -> Diff k v
fromList = Diff . MonoidMap.fromList . fmap (second Seq.singleton)

-- | @'fromListInserts' xs@ creates a @'Diff'@ that inserts all values in @xs@.
fromListInserts :: Ord k => [(k, v)] -> Diff k v
fromListInserts =
  Diff . MonoidMap.fromList . fmap (fmap (Seq.singleton . Insert))

-- | @'fromListDeletes' xs@ creates a @'Diff'@ that deletes all values in @xs@.
fromListDeletes :: Ord k => [k] -> Diff k v
fromListDeletes = Diff . MonoidMap.fromList . fmap (, Seq.singleton Delete)

singleton :: Delta v -> DeltaHistory v
singleton = DeltaHistory . NESeq.singleton

singletonInsert :: v -> DeltaHistory v
singletonInsert = singleton . Insert

singletonDelete :: DeltaHistory v
singletonDelete = singleton Delete

{------------------------------------------------------------------------------
  Deconstruction
------------------------------------------------------------------------------}

last :: DeltaHistory v -> Delta v
last (DeltaHistory (_ NESeq.:||> e)) = e

lastMaybe :: Seq (Delta v) -> Maybe (Delta v)
lastMaybe (_ Seq.:|> e) = Just e
lastMaybe _ = Nothing

{------------------------------------------------------------------------------
  Query
------------------------------------------------------------------------------}

null :: Diff k v -> Bool
null (Diff m) = MonoidMap.null m

size :: Diff k v -> Int
size (Diff m) = MonoidMap.nonNullCount m

-- | @'numInserts' d@ returns the number of inserts in the diff @d@.
--
-- Note: that is, the number of diff histories that have inserts as their last
-- change.
numInserts :: Diff k v -> Int
numInserts (Diff m) = getSum $ foldMap' f m
  where
    f h = case lastMaybe h of
      Just (Insert _) -> 1
      Just  Delete    -> 0
      Nothing         -> 0

-- | @'numDeletes' d@ returns the number of deletes in the diff @d@.
--
-- Note: that is, the number of diff histories that have deletes as their last
-- change.
numDeletes :: Diff k v -> Int
numDeletes (Diff m) = getSum $ foldMap' f m
  where
    f h = case lastMaybe h of
      Just (Insert _) -> 0
      Just  Delete    -> 1
      Nothing         -> 0

{------------------------------------------------------------------------------
  Applying diffs
------------------------------------------------------------------------------}

-- | Applies a diff to a @'Map'@.
applyDiff ::
     Ord k
  => Map k v
  -> Diff k v
  -> Map k v
applyDiff m (Diff diffs) =
    Merge.merge
      Merge.preserveMissing
      (Merge.mapMaybeMissing (\_k s -> lastKeyMaybe s)
      (Merge.zipWithMaybeMatched (\_k _v s -> lastKeyMaybe s)
      m
      (MonoidMap.toMap diffs)
  where
    lastKeyMaybe :: Seq (Delta v) -> Maybe v
    lastKeyMaybe s = extract =<< lastMaybe s
      where
        extract (Insert x) = Just x
        extract Delete     = Nothing

-- | Applies a diff to a @'Map'@ for a specific set of keys.
applyDiffForKeys ::
     Ord k
  => Map k v
  -> Set k
  -> Diff k v
  -> Map k v
applyDiffForKeys m ks (Diff diffs) =
  applyDiff
    m
    $ Diff
    $ MonoidMap.fromMap
    $ MonoidMap.toMap diffs `Map.restrictKeys` (Map.keysSet m `Set.union` ks)

{------------------------------------------------------------------------------
  Folds and traversals
------------------------------------------------------------------------------}

-- | @'foldMap'@ over the last delta in each delta history.
foldMapDelta :: (Monoid m) => (Delta v -> m) -> Diff k v -> m
foldMapDelta f (Diff m) =
  foldMap (foldMap f . lastMaybe) m

-- | Traversal with keys over the last delta in each delta history.
traverseDeltaWithKey_ ::
     Applicative t
  => (k -> Delta v -> t a)
  -> Diff k v
  -> t ()
traverseDeltaWithKey_ f (Diff m) =
    void $ Map.traverseWithKey g $ MonoidMap.toMap m
  where
    g k = traverse (f k) . lastMaybe

{-------------------------------------------------------------------------------
  Filter
-------------------------------------------------------------------------------}

filterOnlyKey :: (k -> Bool) -> Diff k v -> Diff k v
filterOnlyKey f (Diff m) = Diff $ MonoidMap.filterWithKey (const . f) m

mapMaybeSeq :: (v -> Maybe v') -> Seq (Delta v) -> Seq (Delta v')
mapMaybeSeq f = Seq.fromList . Maybe.mapMaybe (traverse f) . toList

mapMaybeDiff :: (v -> Maybe v') -> Diff k v -> Diff k v'
mapMaybeDiff f (Diff d) = Diff $ MonoidMap.map (mapMaybeSeq f) d
