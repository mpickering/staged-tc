{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
module NbEPolarised where

import Data.Kind

data Thunk (a :: Type)
data Comp (a :: Type)

data PE v a where
  PVar :: v a -> PE v a
  PThunk :: NE v a -> PE v (Thunk a)
  PUnit :: PE v ()
  PL :: PE v a -> PE v (Either a b)
  PR :: PE v b -> PE v (Either a b)

data PNf v a where
  PNfVar :: v a -> PNf v a
  PNfThunk :: NNf v a -> PNf v (Thunk a)
  PNfUnit :: PNf v ()
  PNfL :: PNf v a -> PNf v (Either a b)
  PNfR :: PNf v b -> PNf v (Either a b)

data PNe v a where
  PNeApp :: PNe v (a -> b) -> PNf v a -> PNe v b
--  PNeCase :: PNe v (Either a b) -> PNf v
  PNeForce :: v (Thunk a) -> PNe v a

data NE v a where
  NRet :: Run a => PE v a -> NE v (Comp a)
  NBind :: Run a => NE v (Comp a) -> NE v (a -> b) -> NE v b

  NFunc :: (v a -> PE v b) -> NE v (a -> b)
  NForce :: PE v (Thunk a) -> NE v a
  NApp :: NE v (a -> b) -> NE v a -> NE v b
  NCase :: PE v (Either a b) -> NE v (a -> c) -> NE v (b -> c) -> NE v c

data NNf v a where
  NNf :: C v (PNe v a) -> NNf v a
  NNfRet :: C v (PNf v a) -> NNf v (Comp a)

  NNfAbs :: (v a -> NNf v b) -> NNf v (a -> b)
  NNfCase :: v (Either a b) -> (v a -> NNf v r) -> (v b -> NNf v r) -> NNf v r


normN x = run (nreify $ evalN x)

data V1 v a = V1 { evalV1 :: Sem v a }

eval :: PE (V1 v) a -> Sem v a
eval (PVar x) = evalV1 x
eval (PThunk ne) = evalN ne
eval PUnit = ()
eval (PL x) = Left (eval x)
eval (PR x) = Right (eval x)

evalN :: forall v a .  NE (V1 v) a -> Sem v a
evalN (NRet x) = return (eval x)
evalN (NBind (c :: NE z (Comp x)) f) = (evalN f) $ run @x (evalN @_ @(Comp _) c )
evalN (NFunc f) = \x -> eval $ f (V1 x)
evalN (NForce pe) = eval pe
evalN (NApp f x) = (evalN f) (evalN x)
evalN (NCase scrut k1 k2) = either (evalN k1) (evalN k2) (eval scrut)

data V2 a = V2 { evalV2 :: String }

showP :: PE V2 a -> String
showP (PVar x) = evalV2 x
showP (PThunk x) = "[" ++ showN x ++ "]"
showP PUnit      = "()"
showP (PL l)     = "(Left " ++ showP l ++ ")"
showP (PR l)     = "(Right " ++ showP l ++ ")"

showN :: NE V2 a -> String
showN (NRet x) = "(return " ++  showP x ++ ")"
showN (NBind c f) = showN c ++ " >>= \\x -> " ++ showN f
showN (NFunc f)   = "\\x -> " ++ showP (f (V2 "x"))
showN (NForce pe) = "! " ++ showP pe
showN (NApp f x)  = showN f ++ " " ++ showN x
showN (NCase scrut k1 k2) = "either (" ++ showN k1 ++ ") (" ++ showN k2 ++ ") " ++ showP scrut

t1 :: PE v (Either () b)
t1 = PL PUnit

t2 :: PE v (Either a ())
t2 = PR PUnit

c :: PE v a -> NE v (z -> a)
c x = NFunc (\_ -> x)

t3 :: NE v (Either () () -> Thunk (Either () ()))
t3 = NFunc (\x -> PThunk (NCase (PVar x) (c t2) (c t1)))


type C v a = FreeT (Cover v) a

class Run a where
  run :: C v (Sem v a) -> Sem v a

instance Run () where
  run _ = ()

instance Run b => Run (a -> b) where
  run c a = run @b (c <*> pure a)

instance Run (Comp x) where
  run c = c >>= id

type family Sem v a where
   Sem v () = ()
   Sem v (Either a b) = Either (Sem v a) (Sem v b)
   Sem v (Thunk a) = Sem v a
   Sem v (a -> b) = Sem v a -> Sem v b
   Sem v (Comp a) = C v (Sem v a)

instance PRf v () where
  preflect _ = return ()
  preify k   = PNfUnit

instance (PRf v a, PRf v b) => PRf v (Either a b) where
  preflect x = wrap (Cover x (\l -> Left <$> (preflect l)) (\r -> Right <$> (preflect r)))
  preify = either (PNfL . preify) (PNfR . preify)

instance NRf v x => PRf v (Thunk x) where
  preflect x = return $ nreflect (PNeForce x)
  preify = PNfThunk . nreify

instance PRf v a => NRf v (Comp a) where
  nreflect x = wrap (Bind x (\a -> preflect a))
  nreify  x = NNfRet (fmap preify x)

instance (PRf v a, NRf v b) => NRf v (a -> b) where
  nreflect u = \x -> nreflect (PNeApp u (preify x))
  nreify f = NNfAbs (\x ->  sink (fmap (nreify . f) (preflect x)))


  {-
instance Rf v (Either a b) where

instance Rf v (Thunk a) where

instance Rf v (a -> b) where

instance Rf v (Comp a) where
-}

class PRf (v :: Type -> Type) a where
  preflect :: v a -> C v (Sem v a)
  preify :: Sem v a -> PNf v a

class NRf (v :: Type -> Type) a where
  nreflect :: PNe v a -> Sem v a
  nreify :: Sem v a -> NNf v a


data FreeT f a = FreeT { freeT :: forall r . (a -> r) -> (f r -> r) -> r }

wrap :: Functor f => f (FreeT f a) -> FreeT f a
wrap fa = FreeT $ \r w -> w (fmap (\x -> freeT x r w) fa)

data Cover v r where
  Cover :: v (Either a b) -> (v a -> r) -> (v b -> r) -> Cover v r
  Bind  :: PNe v (Comp a) -> (v a -> r) -> Cover v r


instance Functor (Cover v) where
  fmap f (Cover v k1 k2) = Cover v (f . k1) (f . k2)
  fmap f (Bind ne a)     = Bind ne (f . a)


instance Functor (FreeT f) where
  fmap f (FreeT k) = FreeT $ \r w -> k (r . f) w

instance Applicative (FreeT f) where
    pure a = FreeT $ \r w -> r a
    (<*>) gf ga = FreeT $ \r w -> (freeT gf (\f -> freeT ga (\a -> r (f a)) w) w)

instance Monad (FreeT f) where
    return = pure
    (>>=) ga f = FreeT $ \r w -> freeT ga (\a -> freeT (f a) r w) w



data ContT m a = ContT { unGen :: forall r . (a -> m r) -> m r }

sink :: C v (NNf v a) -> NNf v a
sink (FreeT f) = f id alg
  where
    alg (Cover v k1 k2) = NNfCase v k1 k2


instance Functor (ContT m) where
  fmap f (ContT k) = ContT $ \k2 -> k (k2 . f)

instance Applicative (ContT m) where
    pure a = ContT $ \k -> k a
    (<*>) gf ga = ContT $ \k -> unGen gf $ \f -> unGen ga $ \a -> k (f a)

instance Monad (ContT m) where
    return = pure
    (>>=) ga f = ContT $ \k -> unGen ga $ \a -> unGen (f a) k
