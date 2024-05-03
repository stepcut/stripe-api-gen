{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Web.Stripe.Types where

import Control.Applicative (pure, (<$>), (<*>), (<|>))
import Control.Monad (mzero)
import Data.Aeson
  ( FromJSON (parseJSON),
    Object,
    ToJSON (..),
    Value (..),
    (.:),
    (.:?),
  )
import Data.Aeson.Types (typeMismatch)
import Data.Data (Data, Typeable)
import qualified Data.HashMap.Strict as H
import Data.Map (Map)
import Data.Ratio ((%))
import Data.Text (Text, unpack)
import Data.Time (UTCTime)
import Numeric (fromRat, showFFloat)
import Text.Read (lexP, pfail)
import qualified Text.Read as R
import Web.Stripe.OneOf (OneOf (..))
import Web.Stripe.Util (fromSeconds)

deriving instance Ord Value

type family ExpandsTo id :: *

data LineItems
  = LineItems
  deriving (Eq, Data, Ord, Read, Show)

instance FromJSON LineItems where
  parseJSON v = pure undefined

data UseStripeSdk
  = UseStripeSdk
  deriving (Eq, Data, Ord, Read, Show)

instance FromJSON UseStripeSdk where
  parseJSON (Data.Aeson.Object o) = pure UseStripeSdk

data Expandable id
  = ID id
  | Expanded (ExpandsTo id)
  deriving (Typeable)

type instance
  ExpandsTo (OneOf [a, b]) =
    OneOf
      '[ ExpandsTo a,
         ExpandsTo b
       ]

type instance
  ExpandsTo (OneOf [a, b, c]) =
    OneOf
      '[ ExpandsTo a,
         ExpandsTo b,
         ExpandsTo c
       ]

deriving instance
  (Data id, Data (ExpandsTo id)) =>
  Data (Expandable id)

deriving instance
  (Show id, Show (ExpandsTo id)) =>
  Show (Expandable id)

deriving instance
  (Read id, Read (ExpandsTo id)) =>
  Read (Expandable id)

deriving instance (Eq id, Eq (ExpandsTo id)) => Eq (Expandable id)

deriving instance
  (Ord id, Ord (ExpandsTo id)) =>
  Ord (Expandable id)

instance (Typeable a) => Eq (Expandable (OneOf a))

instance (Typeable a) => Data (Expandable (OneOf a))

instance (Typeable a) => Ord (Expandable (OneOf a))

instance (Typeable a) => Read (Expandable (OneOf a))

instance (Typeable a) => Show (Expandable (OneOf a))

instance
  (FromJSON id, FromJSON (ExpandsTo id)) =>
  FromJSON (Expandable id)
  where
  parseJSON v = (ID <$> parseJSON v) <|> (Expanded <$> parseJSON v)

instance FromJSON (Expandable (OneOf rs)) where
  parseJSON _ =
    error "FromJSON (Expandable (OneOf rs)) not implemented yet"

data TimeRange a = TimeRange
  { gt :: (Maybe a),
    gte :: (Maybe a),
    lt :: (Maybe a),
    lte :: (Maybe a)
  }
  deriving (Read, Show, Eq, Ord, Data, Typeable)

data StripeList a = StripeList
  { list :: [a],
    stripeUrl :: Text,
    object :: Text,
    totalCount :: (Maybe Int),
    hasMore :: Bool
  }
  deriving (Eq, Data, Ord, Read, Show)

instance (FromJSON a) => FromJSON (StripeList a) where
  parseJSON (Data.Aeson.Object o) =
    StripeList
      <$> o
      .: "data"
      <*> o
      .: "url"
      <*> o
      .: "object"
      <*> o
      .:? "total_count"
      <*> o
      .: "has_more"

newtype ExpandParams = ExpandParams {getExpandParams :: [Text]}
  deriving (Eq, Data, Ord, Read, Show)

newtype EndingBefore a = EndingBefore {getEndingBefore :: a}
  deriving (Eq, Data, Ord, Read, Show)

newtype StartingAfter a = StartingAfter {getStartingAfter :: a}
  deriving (Eq, Data, Ord, Read, Show)

newtype Limit = Limit {getLimit :: Int}
  deriving (Eq, Data, Ord, Read, Show)

newtype Metadata = Metadata {unMetadata :: [(Text, Text)]}
  deriving (Eq, Data, Ord, Read, Show)

data UpTo
  = Inf
  | UpTo !Integer
  deriving (Eq, Data, Ord, Read, Show)

instance FromJSON UpTo where
  parseJSON (Data.Aeson.String "inf") = pure Inf
  parseJSON v = UpTo <$> parseJSON v

instance FromJSON Metadata where
  parseJSON v = Metadata <$> parseJSON v

data NowOrLater
  = Now
  | Later !UTCTime
  deriving (Eq, Data, Ord, Read, Show)

data Lines a = Lines
  { linesData :: [a],
    linesUrl :: Text,
    linesObject :: Text,
    linesHasMore :: Bool
  }
  deriving (Eq, Data, Ord, Read, Show)

instance (FromJSON a) => FromJSON (Lines a) where
  parseJSON (Data.Aeson.Object o) =
    Lines
      <$> o
      .: "data"
      <*> o
      .: "url"
      <*> o
      .: "object"
      <*> o
      .: "has_more"

data Emptyable a
  = Full !a
  | Empty
  deriving (Eq, Data, Ord, Read, Show)

data Status
  = Active
  | Inactive
  | Pending
  deriving (Eq, Data, Ord, Read, Show)

instance FromJSON Status where
  parseJSON (String c) =
    case c of
      "active" -> pure Active
      "inactive" -> pure Inactive
      "pending" -> pure Pending

newtype AvailableOn
  = AvailableOn UTCTime
  deriving (Read, Show, Eq, Ord, Data, Typeable)

newtype Date
  = Date UTCTime
  deriving (Read, Show, Eq, Ord, Data, Typeable)

data Currency
  = USD
  deriving (Read, Show, Eq, Ord, Data, Typeable)

instance FromJSON Currency where
  parseJSON (String "USD") = pure USD
  parseJSON _ = pure USD

newtype Amount = Amount {getAmount :: Int}
  deriving (Eq, Data, Ord, Read, Show)

instance FromJSON Amount where
  parseJSON a = Amount <$> parseJSON a

emptyTimeRange :: TimeRange a
emptyTimeRange = TimeRange Nothing Nothing Nothing Nothing

showAmount :: Currency -> Int -> String
showAmount cur amt =
  case cur of
    USD -> "$" ++ show2places (currencyDivisor cur amt)
    _ -> show2places (currencyDivisor cur amt) ++ (" " ++ show cur)
  where
    show2places v = showFFloat (Just 2) v ""

currencyDivisor :: Currency -> Int -> Float
currencyDivisor cur =
  case cur of USD -> hundred
  where
    hundred v = fromRat $ (fromIntegral v % 100)
