https://hackage.haskell.org/package/static-closure-0.1.0.0/docs/Control-Static-Closure.html

=> things you can get Name for are allowed

foo_external = 'foo


foo_applied :: Source StaticPtr Int -> Int
foo_applied = App (Var foo) (Lit 0)

foo_applied = [|| foo 0 ||] => [|| $$(findExternalRef @StaticPtr 'foo) 0 ||] => findExteranLRef @StaticPtr 'foo >>= \foo' -> App (Var foo') (Lit 0)



-- Splices type is "Source StaticPtr a"
--
--
-- Simple solution:
--    Don't allow open quotations.
--    Difference between a "variable" and "expression" is more important
foo_applied_applied = [|| $(foo_applied) 1 ||]

lam f = [| \x -> $(f [| x |]) |] -- In environment, x :: forall v . v a

lam f = Lam (\x -> f . Var $ x)



[| \x -> x |] :: Source StaticPtr (a -> a)

eval :: Source Identity StaticPtr a -> a
eval (V x) = x
eval (E v) = derefStaticPtr v
eval (Lam f) = \x -> f x


eval_stpr :: Source StaticPtr a -> ByteString
read_stpr :: ByteString -> IO (Source StaticPtr a)

eval :: Source StaticPtr a -> a



closed_expr :: forall v . Source v a
closed_expr ...


-- Mentioning "Code terms"
-- [|| foo + bar ||] <- external references are turned into "Code" values
open_expr :: Source Code a

foo :: StaticPtr (Int -> Int -> Int)
foo = static bar -- 122 => bar
-- send 122
-- maps 122 => bar

foreign import "baz"...

{-
1. "normal EDSL" - v = Identity      => Anything
2. "staged EDSL" - v  = Code         => Only things which are "quote" imported
3. "static pointers" - v = StaticPtr => Only things in the static pointer table
4. "C modality"      -  v = CPtr     => Only foreign imported things
5. ....
-}



[|| foo + bar ||] -> situation 2

quote :: ExternalRef v => Source v a
[1|| foo + bar ||] -> ...

class ExternalRef m e where
  findExternalRef :: Name a -> m (Source v e a))

Name a => App Identity (EVar a) => EVar (Identity a)

{-
1. Identity case => no typechecking needed, just wrap with Identity constructor.
2. For StaticPtr case, everything is already wrapped in StaticPtr if it's allowed to
be used.
-}



[|| $$(findExternalRef 'foo) + $$(findExternalRef 'bar) ||]

instance ExternalRef StaticPtr where
  findExternalRef :: Name a -> Q (Name (StaticPtr a))
  findExternalRef

  findExternalRef :: Name a -> Q (Name (StaticPtr a))



Source Name a -> Q (Source Identity a)
Source Name a -> Q (Source StaticPtr a)

-- $$(compile $ myexpr)



