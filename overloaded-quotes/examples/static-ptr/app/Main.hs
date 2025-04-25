module Main where

import GHC.IO
import Data.Kind
import Data.Binary hiding (decode, encode)
import GHC.Generics
import GHC.StaticPtr
import Data.Functor.Const
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Dynamic
import Data.Proxy
import Type.Reflection hiding (App)

-- The source language, the result of desugaring a quoted expression.
data Source v a where
  Ext :: forall a v. Typeable a => StaticPtr a -> Source v a
  Var :: v a -> Source v a
  App :: Source v (a -> b) -> Source v a -> Source v b
  Lam :: forall a b v. (Typeable a, Typeable b) => (v a -> Source v b) -> Source v (a -> b)

-- A serializable data type representing computations.
data SE
  = SExt SomeTypeRep StaticKey
  | SVar String
  | SApp SE SE
  | SLam SomeTypeRep SomeTypeRep String SE
  deriving Generic

-- Proof that `SE` is serializable.
instance Binary SE


instance IsStatic (Source v) where
  fromStaticPtr = Ext

-- A desugared quoted expression will essentially have type `forall v. Source v a` for some specific `a`. To encode it, we pick `v = Const String`.

-- Initially the quoted expression must be closed (minus external variables). Therefore we use an empty environment.
encode :: Source (Const String) a -> SE
encode = encode' []

encode' :: [String] -> Source (Const String) a -> SE
encode' env (Ext @a p)         = SExt (someTypeRep (Proxy :: Proxy a)) $ staticKey p
encode' env (Var (Const x)) = SVar x
encode' env (App t u)       = SApp (encode' env t) (encode' env u)
encode' env (Lam @a @b f)         = let x = fresh env in SLam (someTypeRep (Proxy :: Proxy a)) (someTypeRep (Proxy :: Proxy b)) x (encode' (x : env) (f (Const x)))

fresh :: [String] -> String
fresh env = fromJust $ find (`notElem` env) $ map show ['a' ..]


-- On the receiving end of the communicated expression, we need to deserialize `SE` into a regular Haskell term.
-- At the moment this is done in a non-type safe way, perhaps its possible to do better!


-- Attempt using `Dynamic`
decode :: SE -> Dynamic
decode = decode' []

decode' :: [(String, Dynamic)] -> SE -> Dynamic
decode' env (SExt (SomeTypeRep rep) p) | Just HRefl <- typeRep @Type `eqTypeRep` typeRepKind rep =
  Dynamic rep $ deRefStaticPtr $ fromJust $ unsafePerformIO $ unsafeLookupStaticPtr p
decode' env (SVar x) = fromJust $ lookup x env
decode' env (SApp t u) = fromJust $ dynApply (decode' env t) (decode' env u)
decode' env (SLam (SomeTypeRep argRep) (SomeTypeRep retRep) x t) | Just HRefl <- typeRep @Type `eqTypeRep` typeRepKind argRep,  Just HRefl <- typeRep @Type `eqTypeRep` typeRepKind retRep =
    Dynamic (Fun argRep retRep) $ \v -> case decode' ((x, Dynamic argRep v) : env) t of
                                          Dynamic retRep' l | Just HRefl <- eqTypeRep retRep retRep' -> l



foo :: forall v. Source v (Int -> Int)
foo = Lam $ \x -> App (static (\x -> x + 1)) (Var x)


main = do
  let x = decode $ encode foo
  let f :: Int -> Int = fromJust $ fromDynamic @(Int -> Int) x
  print $ f 3
  -- print x