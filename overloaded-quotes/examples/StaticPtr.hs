-- This file gives an example of using quote overloading to implement an EDSL for serializable Haskell expressions.
-- Currently we operate only on the `Source` data type directly, but once the compiler implementation is finished
-- then we can use quoted blocks [|| .. ||] instead of using `Source` data constructors.

{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Lib where

import Data.Binary
import GHC.Generics
import GHC.StaticPtr
import Data.Functor.Const
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Dynamic

-- The source language, the result of desugaring a quoted expression.
data Source v a where
  Ext :: StaticPtr a -> Source v a
  Var :: v a -> Source v a
  App :: Source v (a -> b) -> Source v a -> Source v b
  Lam :: (v a -> Source v b) -> Source v (a -> b)

-- A serializable data type representing computations.
data SE
  = SExt StaticKey
  | SVar String
  | SApp SE SE
  | SLam String SE
  deriving Generic

-- Proof that `SE` is serializable.
instance Binary SE

-- A desugared quoted expression will essentially have type `forall v. Source v a` for some specific `a`. To encode it, we pick `v = Const String`.

-- Initially the quoted expression must be closed (minus external variables). Therefore we use an empty environment.
encode :: Source (Const String) a -> SE
encode = encode' []

encode' :: [String] -> Source (Const String) a -> SE
encode' env (Ext p)         = SExt $ staticKey p
encode' env (Var (Const x)) = SVar x
encode' env (App t u)       = SApp (encode' env t) (encode' env u)
encode' env (Lam f)         = let x = fresh env in SLam x (encode' (x : env) (f (Const x)))

fresh :: [String] -> String
fresh env = fromJust $ find (`notElem` env) $ map show ['a' ..]


-- On the receiving end of the communicated expression, we need to deserialize `SE` into a regular Haskell term.
-- At the moment this is done in a non-type safe way, perhaps its possible to do better!


-- Attempt using `Dynamic`
decode :: SE -> Dynamic
decode = decode' []

decode' :: [(String, Dynamic)] -> SE -> Dynamic
decode' env (SExt p) = _ -- We want to use `unsafeLookupStaticPtr` or something, but we don't know the type of the external. Not sure how to do this.
decode' env (SVar x) = fromJust $ lookup x env
decode' env (SApp t u) = toDyn (fromDyn (decode' env t) $ fromDyn (decode' env u)) -- This also doesn't work because we don't know typing information.
decode' env (SLam x t) = toDyn $ \v -> decode' ((x, v) : env) t
