### Input Program

Considering a very simple example:

```haskell
class Eq a where
  eq :: a -> a -> Bool

instance Eq Int where
  eq = primEq -- Assume that this is an appropriate haskell primitive for checking integer equality.

-- Checks whether three integers are all the same.
threeEq :: Int -> Int -> Int -> Bool
threeEq x y z = eq x y && eq y z
```

### Output Program

The idealised result of specialisation is the following definiton, where the calls to the typeclass function `eq` have been replaced with the Haskell primitive equality.

```haskell
threeEq :: Int -> Int -> Int -> Bool
threeEq x y z = primEq x y && primEq y z
```

### Elaboration Output

An example elaboration is the following:

```haskell
data Eq a = Eq {
  eq :: Code a -> Code a -> Code Bool
}

intEq :: Eq Int
intEq = Eq (\x y -> [| primEq $x $y |])

threeEq :: Code (Int -> Int -> Int -> Bool)
threeEq = [| \x y z -> $(intEq.eq [| x |] [| y |]) && $(intEq.eq [| x |] [| y |]) |]
```

This is still very hand-wavy. In traditional MSP, this implies that threeEq is a compile-time binding which will be inlined everywhere. We most likely want it to be a run-time binding, but this isn't easy to express.

If I remember correctly, a principled way to handle let-insertion (i.e. run-time bindings) is to use a code generation monad based on CPS (e.g. named `Gen`). The result of elaboration would then be, not a Haskell program with top-level bindings, but an expression of type `Gen ()` which generates top-level definitoons when executed.
