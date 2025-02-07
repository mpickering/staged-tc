{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-splices -O0 #-}
module Examples where

import TC

{-
ex_normal, ex_1, ex_2 :: Int -> String
ex_normal = normal intDict

ex_1 x = $$(code_ex_1 intDictCode [|| x ||])

ex_2 x = $$(code_ex_2 intDictCF [|| x ||])

r1, r2, r3 :: Int -> String
r1 = recursive intDict

r2 x = $$(code_ex_recursive intDictCode [|| x ||])

r3 x = $$(code_ex_recursiveCF intDictCF [|| x ||])
-}

r4 x = $$(sinkM $ do
                r <- repr [|| x ||]
                a' <- example_cf_d
                a1 a' r
                )

r5 x = $$(sinkM $ repr [|| x ||] >>= \r -> a1 pair_f r)
