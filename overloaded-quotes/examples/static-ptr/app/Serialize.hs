module Serialize
  ( Source (..),
    decode,
    encode,
    lookupStaticPtr
  )
where

import Data.Binary qualified as B
import Data.Dynamic
import Data.Functor.Const
import Data.Kind
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Proxy
import GHC.Generics
import GHC.IO
import GHC.StaticPtr
import Type.Reflection hiding (App)

data Source v a where
  Ext :: forall a v. (Typeable a) => StaticPtr a -> Source v a
  Var :: v a -> Source v a
  App :: Source v (a -> b) -> Source v a -> Source v b
  Lam :: forall a b v. (Typeable a, Typeable b) => (v a -> Source v b) -> Source v (a -> b)

-- A serializable data type representing computations.
data SE
  = SExt SomeTypeRep StaticKey
  | SVar String
  | SApp SE SE
  | SLam SomeTypeRep String SE
  deriving (Generic)

-- Proof that `SE` is serializable.
-- instance Binary SE

instance IsStatic (Source v) where
  fromStaticPtr = Ext

-- A desugared quoted expression will essentially have type `forall v. Source v a` for some specific `a`. To encode it, we pick `v = Const String`.

-- Initially the quoted expression must be closed (minus external variables). Therefore we use an empty environment.
encode :: Source (Const String) a -> SE
encode = encode' []

encode' :: [String] -> Source (Const String) a -> SE
encode' env (Ext @a p) = SExt (someTypeRep (Proxy :: Proxy a)) $ staticKey p
encode' env (Var (Const x)) = SVar x
encode' env (App t u) = SApp (encode' env t) (encode' env u)
encode' env (Lam @a f) = let x = fresh env in SLam (someTypeRep (Proxy :: Proxy a)) x (encode' (x : env) (f (Const x)))

fresh :: [String] -> String
fresh env = fromJust $ find (`notElem` env) $ map show ['a' ..]

-- On the receiving end of the communicated expression, we need to deserialize `SE` into a regular Haskell term.
-- At the moment this is done in a non-type safe way, perhaps its possible to do better!

-- Attempt using `Dynamic`
-- decode :: SE -> Maybe Dynamic
-- decode = decode' []

-- decode' :: [(String, Dynamic)] -> SE -> Maybe Dynamic
-- decode' env (SExt (SomeTypeRep rep) key) = do
--   HRefl <- isType rep
--   let value = deRefStaticPtr $ fromJust $ unsafePerformIO $ unsafeLookupStaticPtr key
--   pure $ Dynamic rep value
-- decode' env (SVar x) = lookup x env
-- decode' env (SApp t u) = do
--   t' <- decode' env t
--   u' <- decode' env u
--   dynApply t' u'
-- decode' env (SLam (SomeTypeRep argRep) (SomeTypeRep retRep) x t) = do
--   HRefl <- isType argRep
--   HRefl <- isType retRep
--   pure $ Dynamic (Fun argRep retRep) $ \v -> case decode' ((x, Dynamic argRep v) : env) t of
--     Just (Dynamic retRep' l) | Just HRefl <- eqTypeRep retRep retRep' -> l

-- decode'' :: SE -> Maybe ([(String, Dynamic)] -> Dynamic)
-- decode'' = \case
--   SExt (SomeTypeRep rep) key -> do
--     HRefl <- isType rep
--     let value = deRefStaticPtr $ fromJust $ unsafePerformIO $ unsafeLookupStaticPtr key
--     pure $ \_ -> Dynamic rep value
--   -- SVar x -> lookup x env
--   (SLam (SomeTypeRep argRep) (SomeTypeRep retRep) x t) -> do
--     HRefl <- isType argRep
--     HRefl <- isType retRep
--     t' <- decode'' t
--     pure $ \env -> Dynamic (Fun argRep retRep) $ \v -> case decode'' ((x, Dynamic argRep v) : env) t of
--       Just (Dynamic retRep' l) | Just HRefl <- eqTypeRep retRep retRep' -> l

-- Check if a type has kind "*".
isType :: forall {k} {a :: k}. TypeRep a -> Maybe (* :~~: k)
isType rep = typeRep @Type `eqTypeRep` typeRepKind rep

-- Well typed named expressions.

data Var :: [Type] -> Type -> Type where
  Zero :: Var (a : as) a
  Succ :: Var as a -> Var (b : as) a

data Expr :: [Type] -> Type -> Type where
  EExt :: a -> Expr as a
  EVar :: Var as a -> Expr as a
  EApp :: Expr as (a -> b) -> Expr as a -> Expr as b
  ELam :: Expr (a : as) b -> Expr as (a -> b)

data Ctxt :: [Type] -> Type where
  Nil :: Ctxt '[]
  Cons :: String -> TypeRep a -> Ctxt as -> Ctxt (a : as)

-- lookupVar :: forall a as. TypeRep a -> String -> Ctxt as -> Maybe (Var as a)
-- lookupVar rep x = \case
--   Nil -> Nothing
--   Cons y rep' ctxt
--     | x == y -> do
--         HRefl <- eqTypeRep rep rep'
--         Just Zero
--     | otherwise -> Succ <$> lookupVar rep x ctxt

-- check :: Ctxt -> Expr -> Type -> Maybe ()

-- typecheck :: forall as a. TypeRep a -> Ctxt as -> SE -> Maybe (Expr as a)
-- typecheck rep ctxt = \case
--   SExt (SomeTypeRep rep) key -> EExt <$> lookupStaticPtr key
--   SVar x -> EVar <$> lookupVar rep x ctxt
--   SApp t u -> do
--     _ <- typecheck _ ctxt t
--     _

data Check (as :: [*]) :: * where
  Check :: forall (a :: *) as. TypeRep a -> Expr as a -> Check as

data CheckVar (as :: [*]) :: * where
  CheckVar :: forall (a :: *) as. TypeRep a -> Var as a -> CheckVar as

lookupVar :: String -> Ctxt as -> Maybe (CheckVar as)
lookupVar x = \case
  Nil -> Nothing
  Cons y a ctxt
    | x == y -> pure $ CheckVar a Zero
    | otherwise -> do
        CheckVar b n <- lookupVar x ctxt
        pure $ CheckVar b (Succ n)

infer :: Ctxt as -> SE -> Maybe (Check as)
infer ctxt = \case
  SExt (SomeTypeRep a) key -> do
    HRefl <- isType a
    val <- lookupStaticPtr key
    pure $ Check a (EExt val)
  SVar x -> do
    CheckVar a n <- lookupVar x ctxt
    pure $ Check a (EVar n)
  SApp t u -> do
    Check f t' <- infer ctxt t
    case f of
      Fun a b -> do
        HRefl <- isType a
        HRefl <- isType b
        u' <- check ctxt u a
        pure $ Check b $ EApp t' u'
      _ -> Nothing
  SLam (SomeTypeRep a) x t -> do
    HRefl <- isType a
    Check b t' <- infer (Cons x a ctxt) t
    pure $ Check (Fun a b) (ELam t')

check :: Ctxt as -> SE -> TypeRep a -> Maybe (Expr as a)
check ctxt t a = do
  Check b t' <- infer ctxt t
  HRefl <- eqTypeRep a b
  pure t'

data Env (as :: [*]) :: * where
  ENil :: Env '[]
  ECons :: a -> Env as -> Env (a : as)

lookupEnv :: Var as a -> Env as -> a
lookupEnv Zero (ECons x xs) = x
lookupEnv (Succ n) (ECons x xs) = lookupEnv n xs

eval' :: Env as -> Expr as a -> a
eval' env = \case
  EExt x -> x
  EVar x -> lookupEnv x env
  EApp t u -> eval' env t (eval' env u)
  ELam t -> \x -> eval' (ECons x env) t

eval :: Expr '[] a -> a
eval = eval' ENil

lookupStaticPtr :: forall a. StaticKey -> Maybe a
lookupStaticPtr key = do
  let y :: IO (Maybe (StaticPtr a)) = unsafeLookupStaticPtr key
  let z :: Maybe (StaticPtr a) = unsafeDupablePerformIO y
  x :: StaticPtr a <- z
  pure $ deRefStaticPtr x

decode :: TypeRep a -> SE -> Maybe a
decode a s = eval <$> check Nil s a