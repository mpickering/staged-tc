{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StaticPointers #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module TC where

import Data.SOP
import Language.Haskell.TH
import Data.Functor.Identity
import GHC.StaticPtr

type Up = Code Q

upLam :: Up (a -> b) -> (Up a -> Up b)
upLam f x = [|| $$f $$x ||]

-- Should never use this if target is "closure free"
downLam :: (Up a -> Up b) -> Up (a -> b)
downLam f = [|| \x -> $$(f [|| x ||]) ||]

data ShowDict a = ShowDict { showId :: a -> String }

-- Code (ShowDict a)

data ShowDictCode a = ShowDictCode { showCode :: Up (a -> String) }

data CF a where
  C :: (Up a -> Up b) -> CF (a -> b)

appCF :: CF (a -> b) -> Up a -> Up b
appCF (C f) x = f x

data ShowDictCF a = ShowDictCF { showCF :: CF (a -> String) }


intDict :: ShowDict Int
intDict = ShowDict (show @Int)

intDictCode :: ShowDictCode Int
intDictCode = ShowDictCode [|| \x -> show @Int x ||]

intDictCF :: ShowDictCF Int
intDictCF = ShowDictCF $ C $ \x -> [|| show @Int $$x ||]

normal :: ShowDict Int -> Int -> String
normal (ShowDict{..}) x = showId x ++ showId x

code_ex_1 :: ShowDictCode Int -> Up Int -> Up String
code_ex_1 (ShowDictCode{..}) x = [|| $$(upLam showCode x) ++ $$(upLam showCode x) ||]

code_ex_2 :: ShowDictCF Int -> Up Int -> Up String
code_ex_2 (ShowDictCF{..}) x = [|| $$(appCF showCF x) ++ $$(appCF showCF x) ||]


------


recursive :: ShowDict Int -> Int -> String
recursive d@(ShowDict{..}) 0 = ""
recursive d@(ShowDict{..}) n =
  showId n ++ recursive d (n - 1)

code_ex_recursive :: ShowDictCode Int -> Up Int -> Up String
code_ex_recursive (ShowDictCode{..}) x =
  [|| let go 0 = ""
          go n = $$(upLam showCode [|| n ||])  ++ go (n - 1)
      in go $$x ||]

code_ex_recursiveCF :: ShowDictCF Int -> Up Int -> Up String
code_ex_recursiveCF (ShowDictCF{..}) x =
  [|| let go 0 = ""
          go n = $$(appCF showCF [|| n ||])  ++ go (n - 1)
      in go $$x ||]


  {-

Not sure what I was trying to achieve here, was just experimenting with polymorphic
recursion.

data HList xs where
  Nil :: HList '[]
  Cons :: x -> HList xs -> HList (x ': xs)

sNil :: ShowDictCF (HList '[])
sNil = ShowDictCF (C $ \_ -> [|| "[]" ||])

sNilCode :: ShowDictCode (HList '[])
sNilCode = ShowDictCode ([|| \_ -> "[]" ||])
-}

{-
Doesn't work, bug in TTH

sCons :: forall x xs . ShowDictCF x -> ShowDictCF (HList xs) -> ShowDictCF (HList (x ': xs))
sCons (ShowDictCF showA) (ShowDictCF (showXs)) =
    ShowDictCF $ C $ (\xs ->
        [|| case $$xs of
              x `Cons` xs ->
                  $$(appCF showA [|| x ||])
                  ++ ":"
                  ++ $$(appCF showXs [|| xs ||])
        ||])

sCons :: forall x xs . ShowDictCode x -> ShowDictCode (HList xs) -> ShowDictCode (HList (x ': xs))
sCons (ShowDictCode showA) (ShowDictCode (showXs)) =
    ShowDictCode $ (
        [|| \(x `Cons` xs) ->
                  $$(upLam showA [|| x ||])
                  ++ ":"
                  ++ $$(upLam showXs [|| xs ||])
        ||])

-}
{-
sCons :: forall x xs . ShowDictCode x -> ShowDictCode (HList xs) -> ShowDictCode (HList (x ': xs))
sCons (ShowDictCode showA) (ShowDictCode (showXs)) =
    ShowDictCode $ (
        [|| \(x `Cons` xs) ->
                  $$showA x
                  ++ ":"
                  ++ $$showXs xs
        ||])

sTwoList :: ShowDictCode (HList [Int, Int])
sTwoList = sCons intDictCode (sCons intDictCode sNilCode)

sOneList :: ShowDictCode (HList [Int])
sOneList = sCons intDictCode sNilCode
-}

{-
showLayersNil :: ShowDictCode (HList []) -> Up (HList []) -> Up String
showLayersNil (ShowDictCode xs) hlist = [|| $$xs $$hlist ||]

showLayers :: ShowDictCode (HList xs) -> ShowDictCode (HList (x:xs)) -> Up (HList xs) -> Up String
showLayers rec (ShowDictCode showCode) hlist =
  [|| case $$hlist of
        x `Cons` xs -> $$showCode $$hList ++ "\n" ++ $$(showLayers
-}

-------
-- One generic representation of a dictionary?


data ShowX f a = ShowX { showX :: f (Int -> String) }

show_x_id :: ShowX Identity Int
show_x_id = ShowX (Identity (show @Int))

-- In the "Code" modality, the compiler looks for the "ShowX Up" dictionary
-- rather than the "Identity" dictionary as in the normal modality.
show_x_up :: ShowX Up Int
show_x_up = ShowX [|| \x -> show @Int x ||]

show_x_cf :: ShowX CF Int
show_x_cf = ShowX $ C $ \x -> [|| show @Int $$x ||]

showInt :: Int -> String
showInt = show @Int

-- And this works for other modalities as well
show_x_static :: ShowX StaticPtr Int
show_x_static = ShowX $ static showInt


data DictEq a = DictEq { eq :: a -> a -> Bool
                       , ceq :: Up (a -> a -> Bool)
                       }

intDict2 :: DictEq Int
intDict2 = DictEq (==) [|| (==) @Int ||]

data Tree a = Tip a | Branch (Tree a) (Tree a)

eqTree :: DictEq a -> Tree a -> Tree a -> Bool
eqTree d1 =
  let go (Tip a) (Tip b) = eq d1 a b
      go (Branch t1 t2) (Branch r1 r2) = go t1 t2 && go t2 r2
  in go

eqTree :: DictEq a -> Up (Tree a -> Tree a -> Bool)
eqTree d1 = [||
  let go (Tip a) (Tip b) = $$(ceq d1) a b
      go (Branch t1 t2) (Branch r1 r2) = go t1 t2 && go t2 r2
  in go ||]

eqTree2 :: DictEq a -> DictEq (Tree a) -> Tree a -> Tree a -> Bool
eqTree2 d1 d2 (Tip a) (Tip b) = eq d a b
eqTree2 d1 d2 (Branch t1 t2) (Branch r1 r2) = eq d1 d2 t1 t2 && eq d1 d2 r1 r2

--treeDict :: DictEq a -> DictEq (Tree a)
--treeDict d = DictEq eqTree [|| eq treeDict ||]

{-


1. You write the same class definition as before?

class Eq a where
  eq :: a -> a -> Bool

2. New instance for for writing staged instances.
  * What are the rules about the types these instances have to have.

staged instance Eq Int where
  eq :: Code (Int -> Int -> Bool)

staged instance (CodeC' (Eq a)) => Eq (Tree a) where
  eq :: Code (Tree a -> Tree a -> Bool)



3. New constraint form (Staged (Eq Int)) => Provides new instance

4. What is difference from staging with class.

- Representation of dictionary.

Staging with class => CodeC (Eq a) = Code (EqDict a)

Staging with different class => CodeC' (Eq a) = CodeEqDict { ceq :: Code ( a ->  a -> Bool ) }

5. Introduce deriving staging instance methods from other class methods (under certain conditions).


6. Extension .. what about other modalities?

data CF a where
  Pair :: (CF a, CF b) -> CF (a, b)
  Func :: (Up a -> CF b) -> CF (a -> b)
  Prim :: Up a -> CF a

eval :: CF a -> Up a

```

functor CF instance Eq Int where
  eq :: CF (Int -> Int -> Bool)


-- Examples

-- Equality on

1. Non-recursive data-type
2. Recursive data-type

3. Monads, instances for Monad, Applicative, Functor. Reader, State, Tree
3a. "Free monad", capability, tagless final style.


-}










































