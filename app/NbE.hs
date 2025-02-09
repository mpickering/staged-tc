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


{- Inspired by Practical Normalization by Evaluation for EDSLs -}
module NbE where

import Data.Kind
import Control.Monad.Identity

-- Need to remove `Rf` constraints from this definition. They are only to
-- do with the interpretation of this syntax.
data E v x where
  Var :: v x -> E v x
  App :: (Rf v a, Rf v b) => E v (a -> b) -> E v a -> E v b
  Lam :: (Rf v y) => (v x -> E v y) -> E v (x -> y)
  L   :: Rf v x => E v x -> E v (Either x y)
  R   :: Rf v x => E v x -> E v (Either y x)
  U   :: E x ()
  ECase :: (Rf v x, Rf v y) => E v (Either x y) -> E v (x -> r) -> E v (y -> r) -> E v r

e1 :: Rf v () => E v (Either () ())
e1 = L U

e2 :: Rf v () => E v (Either () ())
e2 = R U

e3 :: _ => E v (Either () () -> Either () ())
e3 = Lam (\v -> ECase (Var v) (Lam $ \l -> e2) (Lam $ \_ -> e1))

e4 :: _ => E v (Either () ())
e4 = App e3 e1

norm :: forall a . Rf V1 a => E V1 a -> E V1 a
norm = emb2 . reify . eval @a

quote :: forall a . Rf V1 a => Sem V1 a -> E V1 a
quote = emb2 . reify

-- Directly writing expressions in the semantic domain allows you to write
-- terms in your DSL using the host language.

s1 :: Sem V1 (Either () ())
s1 = pure $ Left ()

s2 :: Sem V1 (Either () ())
s2 = pure $ Right ()

s3 :: Sem V1 (Either () () -> Either () ())
s3 e = e >>= either (const $ s2) (const $ s1)

s4 :: Sem V1 (Either () ())
s4 = s3 s1

class Rf v a where
  type Sem v a :: Type
  reify :: Sem v a -> Nf v a
  reflect :: Ne v a -> Sem v a

data V1 x = V1 { evalVar :: (Sem V1 x)
                  , nameVar :: String}

emb :: Ne v a -> E v a
emb (NVar x) = Var x
emb (NApp f x) = App (emb f) (emb2 x)

emb2 :: Nf v a -> E v a
emb2 (NUp x) = emb x
emb2 NUnit   = U
emb2 (NLam f) = Lam (emb2 . f)
emb2 (NL l) = L (emb2 l)
emb2 (NR r) = R (emb2 r)
emb2 (NCase x k1 k2) = ECase (emb x) (Lam (emb2 . k1)) (Lam (emb2 . k2))

eval :: forall a . Rf V1 a => E V1 a -> Sem V1 a
eval (Var (V1 x _)) = x
eval (App e1 e2) = eval e1 (eval e2)
eval (Lam f)     = \x -> eval (f (V1 x "x"))
eval (L x)       = ContT $ \k -> k (Left (eval x))
eval (R x)       = ContT $ \k -> k (Right (eval x))
eval U           = ()
eval (ECase e (k1 :: E V1 (x -> r)) k2) =
  let e' = eval e
      k1' = eval k1
      k2' = eval k2
      v1l x = V1 x "l"
      v1r x = V1 x "r"
  in eval @r $ emb2 $ rfe $ sink (fmap (either (RfE . NUp . NVar @V1 @r . v1l . k1') (RfE . NUp . NVar @V1 @r . v1r . k2')) e' )


-- Not really correct
showE :: forall a . Rf V1 a => E V1 a -> String
showE (Var (V1 _ v)) = v
showE (App e1 e2) = "(" ++ showE e1 ++ " " ++ showE e2 ++ ")"
showE (Lam f) = "(\\x -> " ++ showE (f (V1 undefined "x")) ++ ")"
showE (L x) = "(L " ++ showE x ++ ")"
showE (R x) = "(R " ++ showE x ++ ")"
showE U = "()"
showE (ECase s k1 k2) = "(either " ++ showE s ++ " " ++ showE k1 ++ " " ++ showE k2 ++ ")"



instance (Rf V1 a, Rf V1 b) => Rf V1 (a -> b) where
  type Sem V1 (a -> b) = Sem V1 a -> Sem V1 b

  reify f = NLam $ \(V1 x _) -> reify (f x)

  reflect n = \x -> reflect (NApp n (reify x))

instance Rf V1 () where
  type Sem V1 () = ()
  reify _ = NUnit
  reflect _ = ()

instance (Rf V1 a, Rf V1 b) => Rf V1 (Either a b) where
  type Sem V1 (Either a b) = ContT (RfE V1) (Either (Sem V1 a) (Sem V1 b))

  reify k = rfe (unGen k (either (RfE . NL . reify) (RfE . NR . reify)))

  reflect n = ContT $ \k -> RfE $ NCase n (rfe . k . Left . evalVar) (rfe . k . Right . evalVar)


data ContT m a = ContT { unGen :: forall r . (a -> m r) -> m r }

data RfE v a = RfE { rfe :: Rf v a => Nf v a }

sink :: ContT m (m a) -> m a
sink (ContT m) = m id

sinkI :: C a -> a
sinkI (ContT k) = runIdentity $ k pure

type C = ContT Identity

runGen :: C a -> (a -> r) -> r
runGen (ContT f) k = runIdentity $ f (pure . k)

gen :: (forall r . (a -> r) -> r) -> C a
gen f = ContT $ \k -> pure $ f (runIdentity . k)

instance Functor (ContT m) where
  fmap f (ContT k) = ContT $ \k2 -> k (k2 . f)

instance Applicative (ContT m) where
    pure a = ContT $ \k -> k a
    (<*>) gf ga = ContT $ \k -> unGen gf $ \f -> unGen ga $ \a -> k (f a)

instance Monad (ContT m) where
    return = pure
    (>>=) ga f = ContT $ \k -> unGen ga $ \a -> unGen (f a) k




data Ne v x where
  NVar :: v x -> Ne v x
  NApp :: (Rf v a, Rf v b) => Ne v (a -> b) -> Nf v a -> Ne v b

data Nf v x where
  NUp :: Ne v x -> Nf v x
  NUnit :: Nf v ()
  NLam  :: Rf v y => (v x -> Nf v y) -> Nf v (x -> y)
  NL :: Rf v a => Nf v a -> Nf v (Either a z)
  NR :: Rf v b => Nf v b -> Nf v (Either z b)
  NCase  :: (Rf v a, Rf v b, Rf v r) => Ne v (Either a b) -> (v a -> Nf v r) -> (v b -> Nf v r) -> Nf v r




