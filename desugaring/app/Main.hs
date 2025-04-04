{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications, ScopedTypeVariables #-}
module Main where

import Generics.SOP
import Data.Maybe
import Control.Applicative

main :: IO ()
main = print $ interpret term

data Source v a where
  Var :: v a -> Source v a
  Constr :: Generic a => SOP (Source v) (Code a) -> Source v a
  Case :: forall b v a. Generic b => Source v b -> [Clause v b a] -> Source v a
  Int' :: Int -> Source v Int

data Clause v b a where
  Clause :: forall v b a. (SOP v (Code b) -> Maybe (Source v a)) -> Clause v b a

-- Pattern DSL
-- Write Pat data type

interpret :: Source I a -> a
interpret (Var (I x)) = x
interpret (Int' n) = n
interpret (Constr x) = to $ hmap (I . interpret) x
interpret (Case x cs) = do
  let x' = from (interpret x)
  fromJust $ asum $ map (flip interpretClause x') cs

interpretClause :: Clause I b a -> SOP I (Code b) -> Maybe a
interpretClause (Clause f) = \x -> interpret <$> f x

cl :: SOP v (Code (Either Int a)) -> Maybe (Source v Int)
cl (SOP (Z (x :* Nil))) = Just (Var x)
cl _ = Nothing

cl' :: SOP v (Code (Either Int a)) -> Maybe (Source v Int)
cl' (SOP (S (Z (_ :* Nil)))) = Just (Int' 0)
cl' _ = Nothing

term :: forall v. Source v Int
term = Case @(Either Int Int) (Constr ((SOP (S (Z (Int' 3 :* Nil))))))
  [
    Clause @v cl, Clause cl'
  ]
