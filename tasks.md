1. What happens in the source language to provide instances?
    * Can we take an existing class instance and provide the right evidence for the code versions?
    * MP intuition: Can reuse existing ones for Code (a -> String)
                  : Cannot reuse for (Code a -> Code String).

    * Does it make sense to write separate runtime vs compile time instances?

    * What if someone already is already writing Code in their type classes.
        * "Use a type class" vs "use staged version of a type class".

2. Type system

    * Source language + type classes + instance definitions
    * Constraint language - Normal type class constraints + "staged constraints"
        -- Unlike "staging with class" (where constraints are levelled), constraints only exist at level 0. <---- primary research question, using a language with type classes to do code generation BUT you use existing instances.

        -- Constraint solving is not modified. Normal constraint system with a special form of
           constraint.

    * Elaboration semantics, source language elaborated into core language
        - Elaborating "normal instances" into "staged instances" <--- primary reasearch question


    * Type class abstraction no longer exists in the core lanuage (which is constructive, because
      target language does not contain type classes or type class evidence).

2. "Specialisation is still is achieced with the simple "Code (a -> String)" version.



Principle 1: If you want specialisation, you have to write something yourself to achieve that.


Code (Int -> String)

== [|| .... ||]

Code Int -> Code String


Int -> Code String

-- Recursion via class instance
instance (Eq a) => Eq [a] where
    [] == [] = True
    (x:xs) == (y:ys) = x == y && xs == ys

1. It is trivial to work out where the recursion is, because the evidence is passed into
those calls.
2. What literature is there about this problem.
3. We know the user does not want a loop at compile time.


aEq :: Code (a -> a -> Bool)

lEq :: Code ([a] -> [a] -> Bool)

lEq = [|| \xs ys -> let go [] [] = []
                        go (x:xs) (y:ys) = $$(aEq) x y && go xs ys
                    in go xs ys ||]

lEq = [|| \xs ys -> fix (\r -> let go [] [] = []
                        go (x:xs) (y:ys) = $$(aEq) x y && go xs ys
                    in go xs ys ||]

Code (Eq [a] => [a] -> [a] -> Bool)
lEq = [| lEqCode |]

-- W

-- Theorem: Elaboration does not result in non-termination.

[|| $$(power (1+1))  ||]

[|| $$(staged show) ||]

* Write examples in the surface language and what the expected elaboration is
    * Decide which features of type classes we wish to support
        * Superclasses
        * Recursion
* Synatax for selecting the "Code version" "staged show"
    - Constraint form: CodeC (Show a) OR add both into the same dictionary
*
*

"Does the dictionary contain both staged and unstaged versions".

## Let Insertion

Ellis: Non issue

Needs some discussion in the paper.

What is the point of doing let insertion for specialisations, are you not defeating the purpose.

"Define your own specialisation"

More in the spirit of staged programming, giving the user control.
