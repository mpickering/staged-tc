To specialise typeclasses, we must first monomorphise. However, not all functions are monomorphisable - specifically, when the function uses polymorphic recursion, monomorphisation might not be possible.

Consider this example taken from [Wikipedia](https://en.wikipedia.org/wiki/Polymorphic_recursion):

```haskell
data Nested a = a :<: (Nested [a]) | Epsilon
infixr 5 :<:

nested = 1 :<: [2,3,4] :<: [[5,6],[7],[8,9]] :<: Epsilon

length :: Nested a -> Int
length Epsilon    = 0
length (_ :<: xs) = 1 + length xs
```

On each recursive call to `length` we instantiate the type variable `a` differently. First we pass `[a]`, then `[[a]]`, and so on. This makes it impossible to monomorphise.

Another example of polymorphic recursion which does not use a data type:

```haskell
foo :: forall a. a
foo = fst $ foo @(a, a)
```

Obviously this example doesn't terminate, but it is valid Haskell code and so should be handled.
