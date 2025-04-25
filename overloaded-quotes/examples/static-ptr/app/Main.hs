module Main where

import Data.Dynamic (fromDynamic)
import Data.Maybe (fromJust)
import Serialize
import Type.Reflection (typeRep)
import GHC.StaticPtr

foo :: forall v. Source v (Int -> Int)
foo = Lam $ \x -> App (static (+ 1)) (Var x)

foo' :: forall v. Source v (Int -> Int)
foo' = static (\x -> x + 1)


add1 :: Int -> Int
add1 x = x + 1

main = do
  let f = fromJust $ decode (typeRep @(Int -> Int)) $ encode foo'
  print $ f 3
  -- let f :: Int -> Int = fromJust $ lookupStaticPtr $ staticKey (static add1)
  -- print $ f 3