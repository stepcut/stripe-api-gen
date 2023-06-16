{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language KindSignatures #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language UndecidableInstances #-}

module Web.Stripe.OneOf where

import Data.Typeable (Typeable, typeOf)
import GHC.TypeLits

import Data.Proxy (Proxy(..))

data MemberTest
  = NotFound ErrorMessage
  | Found

type family IsMember x ys where
  IsMember x '[] = 'NotFound ('Text "Not found: " ':<>: 'ShowType x)
  IsMember x (x ': ys) = 'Found
  IsMember x (y ': ys) = IsMember x ys
  IsMember x ys = IsMember x ys

data OneOf (n :: [k]) where
  Empty :: OneOf s
  Val   :: e -> OneOf (e ': s)
  NoVal :: OneOf s -> OneOf (e ': s)

deriving instance Typeable k => Typeable (OneOf (n :: [k]))

instance Show (OneOf '[]) where
  show Empty = "{}"

type family DeleteList e xs where
  DeleteList x '[] = '[]
  DeleteList x (x ': ys) = ys
  DeleteList x (y ': ys) = (y ': (DeleteList x ys))

type family DeleteOneOf e xs where
  DeleteOneOf x (OneOf ys) = OneOf (DeleteList x ys)

-- > runExcept (throwMember (1.5 :: Float) :: ExceptT (OneOf '[S
instance (Show e, Typeable e, Show (OneOf s)) => Show (OneOf (e ': s)) where
  show (Val e) = "(Val (" <> show e <> " :: " <> show (typeOf e) <> "))"
  show (NoVal o) = show o
  show Empty  = "{}"

instance (Ord (OneOf s)) => Eq (OneOf s) where
  a == b = compare a b == EQ

instance Ord (OneOf '[]) where
  compare _ _ = EQ

instance (Ord e, Ord (OneOf s)) => Ord (OneOf (e ': s)) where
  compare Empty Empty = EQ
  compare Empty _ = LT
  compare _ Empty = GT
  compare (Val e1) (Val e2) = compare e1 e2
  compare (Val _) _ = LT
  compare _ (Val _) = GT
  compare (NoVal o1) (NoVal o2) = compare o1 o2 -- right?

class (IsMember e es ~ 'Found) => Member e es where
  set :: e -> OneOf es
  get :: OneOf es -> Maybe e
  delete :: Proxy e -> OneOf es -> DeleteOneOf e (OneOf es)

instance {-# OVERLAPS #-} Member e (e ': xs) where
  set e = Val e
  get (Val e) = Just e
  get (NoVal _) = Nothing
  get Empty = error "impossible"
  delete _ (Val _e) = Empty
  delete _ (NoVal o) = o
  delete _ Empty = Empty

instance {-# OVERLAPS #-} (IsMember e (f:xs) ~ 'Found, Member e xs, DeleteList e (f:xs) ~ (f : DeleteList e xs)) => Member e (f ': xs) where
  set e = NoVal (set e)
  get (NoVal o) = get o
  get (Val _e) = Nothing
  get Empty = error "impossible"
  delete _p (Val v) = (Val v) -- :: OneOf (f ': (DeleteList e xs))
  delete p (NoVal o) = NoVal (delete p o)
  delete _p Empty = Empty
