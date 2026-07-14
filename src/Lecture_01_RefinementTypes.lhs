Refinement Types 
============

[Refinement types](https://www.cs.cmu.edu/~fp/papers/pldi91.pdf) refine
the types of a target language with logical predicates
to enforce a variety of invariants at compile time, 
that cannot be enforced by the target language's type system.

They exists for various languages, including [Haskell](https://dl.acm.org/doi/10.1145/2628136.2628161), [Scala](https://arxiv.org/abs/2605.08369), and [Rust](https://dl.acm.org/doi/10.1145/3591283).
If you want to extend your language with refinement types, check our [tutorial](https://dl.acm.org/doi/10.1561/2500000032).


In this course, we will learn the refinement type system 
of Liquid Haskell. 


If you follow this course via a browser, 
you can just click the check button that exists on the code spinnets 
to run Liquid Haskell on your file. 
Otherwise, you can download the source code of these notes from [github](https://github.com/nikivazou/FLoC-2026) and run Liquid Haskell on your local machine.
If you follow it on an editor, then compile the code using the Haskell compiler 
and turn on the `Liquid Haskell plugin`, but uncommenting the following line:

\begin{code}

module Lecture_01_RefinementTypes where
import Prelude hiding (replicate, take, drop)
\end{code}


Either way, you can now use the `Liquid Haskell` type checker,
for example to check that division by zero is not possible.

\begin{code}
test :: Int -> Int
test x = 42 `div` 2
\end{code}

If we call `div` with zero, directly or even indirectly via the `x` argument, 
then at runtime we will get a division by zero error.

~~~~~{.ghci}
ghci> test 0
*** Exception: divide by zero
~~~~~

Liquid Haskell comes with a refined type for the division operator 
that specified that the second argument must be non-zero.

~~~~~{.spec}
div :: Int -> {v:Int | v /= 0} -> Int
~~~~~

The above type specifies that the second argument must be non-zero
and is automatically checked at compile time, using an SMT solver.
Today, we will learn how these checks are performed, and how to
write and use refined types in Haskell.


Basic Refinement Types
----------------------

Did you note that `2` is a good argument for the division operator? 

But, what is the type of `2`?



In Haskell `2:Int`, but the same value can have many different refinement types. 
A basic refinement type has the form 

$$ \{ v:b \mid p \} $$
where $b$ is the base type (e.g., `Int`, `Bool`, etc.) and $p$ is a logical predicate.


The type of `2` is the signleton type `{v:Int | v == 2}`.
But an external SMT solver can relax the type to any type that is implied by the equality, for example `{v:Int | v /= 0}`.

Concretely, refinement types are using the SMT to check subtyping. 
For the `0` case, the subtyping check is:

~~~{.spec}
                             forall v. v = 0 => v != 0
                          --------------------------------
  0:{v:Int | v = 0 }    {v:Int | v = 0 } <: {v:Int | v != 0} 
 -------------------------------------------------------------
                0 :: {v:Int | v != 0} 
~~~

The SMT rejects the implication, thus type checking fails! 

For the `2` case, the subtyping succeeds:

~~~{.spec}
                               forall v. v = 2 => v != 0
                           --------------------------------
   0:{v:Int | v = 2 }    {v:Int | v = 2 } <: {v:Int | v != 0}   
 -------------------------------------------------------------
                2 :: {v:Int | v != 0} 
~~~


So, types are _implicitly casted_ via _semantic subtyping_, which is automatically checked by the SMT solver.

Pre- and Post-Conditions
------------------------

Refinement types are used to specify function's 
requirements, i.e., _preconditions_ and 
guarantees, i.e.,  _postconditions_.

For example, we can give `take` a type that says that

- if the index `i` is in bounds, 
- then the result is a list of length `i`.

~~~{.spec}
{-@ take :: i:Nat -> xs:{[a] | i < len xs} -> {v:[a] | len v = i} @-}
~~~

Now let's use `take`:

\begin{code}

test1 :: [Int] -> Int -> [Int]
test1 xs i = take i xs

\end{code}

The type error here is telling us what is wrong. 

- Let's first use a runtime check to fix it! 
- Next, let's replace the runtime check with a Liquid Haskell refinement type.
- Finally, let's strengthen the refinement type to allow us to divide `42` with all the elements we took. 


This example revealed many unique features of verification with Liquid Haskell. 
It is:

1. _path sensitive_, i.e., runtime checks can be used to guide the verification, 
2. _type based_, i.e., we can specify behaviors of collection of data, and 
3. _SMT automated_, i.e., there is no need for user explicit proofs.  



Recursive Functions
--------------------

Let's now define the `take` function.

\begin{code}
{-@ take :: i:Nat -> xs:{[a] | i < len xs}
         -> {v:[a] | len v = i} @-}
take :: Int -> [a] -> [a]
take = undefined 
\end{code}

When defining a function, 
Liquid Haskell requires both the refined and unrefined types.
(GHC does not see the refinement types, which are provided as comments.)
But, for each function Liquid Haskell checks that is 
_total_ (i.e., all cases are covered) 
and _terminating_ (i.e., recursive call is on a smaller input)
 (which can be deactivated with the 
 `--no-totality` and  `--no-termination` flags respectively).  


Dually, let's define the `drop` function.

\begin{code}
{-@ drop :: i:Nat -> xs:{[a] | i < len xs} -> [a] @-}
drop :: Int -> [a] -> [a]
drop = undefined 
\end{code}


Using `take` and `drop` we can now define the `chunk` function that splits a list into chunks of size `i`.

\begin{code}

chunk :: Int -> [a] -> [[a]]
chunk i xs | length xs <= i || i <= 1 
  = [xs]
chunk i xs 
  = take i xs : chunk i (drop i xs)
\end{code}

Liquid Haskell gives a termination error! 
Does `chunk` terminate? 


To show termination we need to 
1. define a _termination metric_ and
2. refine the postcondition of `drop`! 


Summary
-------
We saw how to use Liquid Haskell to _automatically_
prove light program properties, i.e., division by zero and safe indexing. 
Such verification is _path sensitive_, _type based_, and _SMT automated_.
For more information, check out the Liquid Haskell 
[documentation](https://ucsd-progsys.github.io/liquidhaskell/),
[tutorial](https://ucsd-progsys.github.io/liquidhaskell-tutorial/), and 
[github](https://github.com/ucsd-progsys/liquidhaskell). 

Next, we will see how Liquid Haskell can be used to manually prove properties about 
Haskell functions.
For example, can we now prove that `take` and `drop` reconstruct the original list?

~~~{.spec}
forall i. xs.  xs == take i xs ++ drop i xs 
~~~

Yes, using [theorem proving](https://nikivazou.github.io/floc26/TheoremProving.html)! 
