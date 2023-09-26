{-# language DeriveDataTypeable #-}
module HaddockTest where

import Data.Data

type UTCTime = ()
type FixMe = ()
type SubscriptionId = String

foo :: -- | comment before a
       a
     -> b -- ^ comment after c
     -> ()
foo _ _ = ()

const ::
  -- |documentation for a!
  a
  -> b
     -> -- |documentation for a!
        a
const x _ = x


data Subscription
  = Subscription { -- | application
                  application :: !FixMe, 
                  application_fee_percent :: !FixMe,
                  automatic_tax :: !FixMe,
                  billing_cycle_anchor :: !UTCTime,
                  billing_thresholds :: !FixMe,
                  cancel_at :: !(Maybe UTCTime),
                  cancel_at_period_end :: !Bool,
                  canceled_at :: !(Maybe UTCTime),
                  cancellation_details :: !FixMe,
                  collection_method :: !FixMe,
                  created :: !UTCTime,
                  currency :: !FixMe,
                  current_period_end :: !UTCTime,
                  current_period_start :: !UTCTime,
                  customer :: !FixMe,
                  days_until_due :: !(Maybe Int),
                  default_payment_method :: !FixMe,
                  default_source :: !FixMe,
                  default_tax_rates :: !FixMe,
                  description :: !FixMe,
                  discount :: !FixMe,
                  ended_at :: !(Maybe UTCTime),
                  id :: !SubscriptionId,
                  items :: !FixMe,
                  latest_invoice :: !FixMe,
                  livemode :: !Bool,
                  metadata :: !FixMe,
                  next_pending_invoice_item_invoice :: !(Maybe UTCTime),
                  object :: !FixMe,
                  on_behalf_of :: !FixMe,
                  pause_collection :: !FixMe,
                  payment_settings :: !FixMe,
                  pending_invoice_item_interval :: !FixMe,
                  pending_setup_intent :: !FixMe,
                  pending_update :: !FixMe,
                  schedule :: !FixMe,
                  start_date :: !UTCTime,
                  status :: !FixMe,
                  test_clock :: !FixMe,
                  transfer_data :: !FixMe,
                  trial_end :: !(Maybe UTCTime),
                  trial_settings :: !FixMe,
                  trial_start :: !(Maybe UTCTime)}
  deriving (Eq, Data, Ord, Read, Show)
