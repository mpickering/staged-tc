{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StaticPointers #-}
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







