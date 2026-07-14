Data Propositions and Higher-Order Reasoning
=========================

\begin{code}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

{-@ LIQUID "--ple"           @-}
{-@ LIQUID "--etabeta"       @-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--dependantcase" @-}
{-@ LIQUID "--allow-unsafe-constructors" @-}

module Lecture_03_DataPropositions where

import Prelude hiding ((.))
import Language.Haskell.Liquid.ProofCombinators

{-@ infix $    @-}
{-@ infix .    @-}
\end{code}

This lecture describes [data propositions](https://dl.acm.org/doi/pdf/10.1145/3632912)
a feature of Liquid Haskell that mimics Rocq's inductive predicates. 
We present them if three steps. 
We start with simple refined data types.
Then, we present the simplest data proposition, that encodes `Even` numbers. 
Finally, we present a more complex example, 
that encodes the semantics of a stack machine.


Refined Data Types
--------------------

Liquid Haskell allows to write invariants on data types.
As an example, consider a data type encoding the date. 

\begin{code}

data Date = Date
  { day   :: Int
  , month :: Int
  , year  :: Int
  }
\end{code}

We could like to enforce that the day is between 1 and 31, 
the month is between 1 and 12, and the year is positive.
Liquid Haskell enforces these invariants with a refined data definition:

\begin{code}

{-@ data Date = Date
  { day   :: {v:Int | 1 <= v && v <= 31}
  , month :: {v:Int | 1 <= v && v <= 12}
  , year  :: {v:Int | 0 < v}
  }
@-}
\end{code}

The refined data definition is 
internally converted into refined types for the data constructor `Date`:

~~~{.spec}
Date :: {v:Int | 1 <= v && v <= 31} 
     -> {v:Int | 1 <= v && v <= 12} 
     -> {v:Int | 0 < v} 
     -> Date
~~~

In other words, by using refined input types for `Date` 
we have automatically converted it into a *smart* constructor 
that ensures that every instance of a `Date` is legal. 
Consequently, LiquidHaskell verifies:

\begin{code}
{-@ goodDate :: Date @-}
goodDate :: Date
goodDate = Date 15 7 2026
\end{code}

But it rejects a `badDate`:

\begin{code}
{-@ ignore badDate @-}
{-@ badDate :: Date @-}
badDate :: Date
badDate = Date 7 15 2026
\end{code}

Such kind of invariants appear often in programs 
to, for example, encode dependencies between data fields,
sizes or properties of data structures, like red-black trees, heaps, etc.



Data Propositions: Even Numbers
------------

Using refined data types we encode data propositions, 
that essentially axiomatize the behavior of 
predicates in the data type definitions, without actually giving 
a Haskell definition.

They are very similar to Rocq's 
[inductive predicates](http://adam.chlipala.net/cpdt/html/Predicates.html).
Thus, let's look at the using the textbook example of even numbers.

First, we define the data type of natural numbers.

\begin{code}
data N = Z | S N 
\end{code}

Then, we _axiomatize_ the proposition that a number is even.

\begin{code}
data EVEN where 
    E0 :: EVEN 
    E2 :: N -> EVEN -> EVEN

data Eveness = EVEN N 

{-@ data EVEN where 
     E0 :: Prop (EVEN Z)
     E2 :: n:N -> Prop (EVEN n) -> Prop (EVEN (S (S n))) @-}
\end{code}

The two constructors `E0` and `E2` axiomatize the evenness of numbers.
`E0` states that `Z` is even and `E2` states that if `n` is even, 
then `S (S n)` is also even.

The definition is using the `Prop` type, 
that converts expressions into proof objects.

\begin{code}

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

\end{code}

Further, it requires the unrefined `Even` Haskell definition 
as well as an `EVEN` data constructor.


There are two important points in this construction. 

- First, there is no function that computes evens, thus 
there is _no termination check_, meaning, that using data propositions 
one can encode non-terminating computations. 

- Second, the data proposition `EVEN` is a _proof object_,
thus an `Even` value, gives us information _how_ the proof was constructed.



Construction of Even Numbers
----------------------------

Let's construct some even numbers using the `EVEN` data proposition.

\begin{code}
even0, even2, even4 :: EVEN
{-@ even0 :: Prop (EVEN Z) @-}
even0 = undefined 

{-@ even2 :: Prop (EVEN (S (S Z))) @-}
even2 = undefined

{-@ even4 :: Prop (EVEN (S (S (S (S Z))))) @-}
even4 = undefined
\end{code}

**Question:** Fill in the above definitions to construct the even numbers `0`, `2`, and `4`.

<details>
<summary>**Solution**</summary>
<p> _The terms are defined as follows:_</p>

~~~{.spec}
even0 = E0
even2 = E2 Z even0
even4 = E2 (S (S Z)) even2
~~~
</details>


Since `EVEN` is a proof object one can inspect it, 
to, for example, show contradictions. 

\begin{code}
even1_false :: EVEN -> () 
{-@ even1_false :: Prop (EVEN (S Z)) -> {v:() | false} @-}
even1_false _ = undefined
\end{code}

**Question:** Show that `S Z` is not even, by inspection. 

<details>
<summary>**Solution**</summary>
<p> _The term is defined as follows:_</p>

~~~{.spec}
even1_false E0       = ()
even1_false (E2 n p) = even1_false p
~~~
</details>


Functions on Even Numbers
-------------------------

As a first function on even numbers, let's define a function that
takes a non zero, even number and returns its predecessor.
That is, each even number, 
other than `0`, can be written as `2 + n`, for some `n`.

\begin{code}
even_plus_2 :: N -> EVEN -> (N,()) 
{-@ even_plus_2 :: n:{N | n /= Z} 
                -> Prop (EVEN n) 
                -> (m::N, {v:() | n == S (S m)}) @-}
even_plus_2 _ _ = undefined 
\end{code}

**Question:** Fill in the definition of the `even_plus_2` function.

<details>
<summary>**Solution**</summary>
<p> _The term is defined as follows:_</p>

~~~{.spec}
even_plus_2 _ (E2 n _) = (n,()) 
~~~
</details>


As a final exercise, 
let's show that the sum of two even numbers is also even.

To do so, we first define the `plus` function:

\begin{code}
{-@ reflect plus @-}
plus :: N -> N -> N
plus Z     m = m
plus (S n) m = S (plus n m)
\end{code}

**Question:** Fill in the definition of the `even_plus` function.

\begin{code}
even_plus :: N -> N -> EVEN -> EVEN -> EVEN 
{-@ even_plus :: n:N -> m:N 
              -> Prop (EVEN n) -> Prop (EVEN m) 
              -> Prop (EVEN (plus n m)) @-}
even_plus _ _ _ _ = undefined 
\end{code}


<details>
<summary>**Solution**</summary>
<p> _The term is defined as follows:_</p>

~~~{.spec}
even_plus Z m pn pm 
  = pm 
even_plus n m pn@(E2 _ pn') pm 
  = E2 (plus n' m) (even_plus n' m pn' pm)
  where (n',_) = even_plus_2 n pn 
~~~
</details>




Case Study: A Correct-by-Construction Compiler
---------------------------------------------------

Data propositions are very useful to encode the semantics of programs.
In this last part, we show how to use data propositions to encode 
the semantics of a stack machine.

This example is presented in [PLEX OOPSLA'26 paper](https://dl.acm.org/doi/epdf/10.1145/3798248) 
that extends Liquid Haskell's PLE solver with higher-order reasoning.
It is based on the [correct-by-construction compiler](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/calculating-correct-compilers/70AA17724EBCA4182B1B2B522362A9AF?utm_campaign=shareaholic&utm_medium=copy_link&utm_source=bookmark)
previously mechanized in Agda. 




**Expression Language:**
The source of the compiler is a simple expression language:

\begin{code}

data Expr where
  EConst :: Int -> Expr
  EAdd   :: Expr -> Expr -> Expr
  EMul   :: Expr -> Expr -> Expr
  ENeg   :: Expr -> Expr
\end{code}



The meaning of an expression is given by `eval`.

\begin{code}

{-@ reflect eval @-}
eval :: Expr -> Int
eval (EConst x) = x
eval (EAdd e1 e2) = eval e1 + eval e2
eval (EMul e1 e2) = eval e1 * eval e2
eval (ENeg e)     = - (eval e)

\end{code}


**The Stack Machine:**
The target language is a stack machine with three instructions.

\begin{code}

type Stack = [Int]

data OpCode where
  OpPush :: Int -> OpCode
  OpAdd :: OpCode
  OpMul :: OpCode

\end{code}


Each instruction denotes a stack transformer.

\begin{code}

{-@ reflect push @-}
push :: Int -> Stack -> Stack
push v s = v : s

{-@ reflect execOpCode @-}
execOpCode :: OpCode -> Stack -> Stack
execOpCode (OpPush x) = push x
execOpCode OpAdd      = \case (x : y : xs) -> (y + x) : xs
execOpCode OpMul      = \case (x : y : xs) -> (y * x) : xs

\end{code}


The `OpAdd` and `OpMul` cases need at least two stack elements. Instead of
leaving that as a partial function, we introduce a reflected function
that computes how many stack elements an opcode requires.

\begin{code}
{-@ reflect minStackSize @-}
minStackSize :: OpCode -> Int
minStackSize (OpPush x) = 0
minStackSize _          = 2

\end{code}

Now `execOpCode` can be given a precise precondition:


\begin{code}
{-@ execOpCode :: o:OpCode 
               -> { v:Stack | len v >= minStackSize o } 
               -> Stack @-}
\end{code}

This is a typical refinement type: the operation determines the required shape
of the stack.


Data Propositions: Programs for the Stack Machine
-----------------------------------------------------

A stack-machine program is essentially a list of opcodes. But for a
correct-by-construction compiler, a plain list is too weak. We want the program
to carry its semantics in its type.

Concretely, we will use data propositions to index programs by their semantics: 

\begin{code}
data PROGRAM = Program (Stack -> Stack)
\end{code}


The index is a function from stacks to stacks. A value of type `Program p`
represents a program whose semantics is the stack transformer `p`.

The indexed program constructors the following
shape:

\begin{code}

data Program where
{-@ PNil :: Prop (Program id) @-}
  PNil :: Program
{-@ PCons :: op:OpCode
          -> p:(Stack -> { v:Stack | len v >= minStackSize op }) 
          -> Prop (Program p)
          -> Prop (Program (execOpCode op . p)) @-}
  PCons :: OpCode -> (Stack -> Stack) -> Program -> Program


\end{code}

Read the constructors as follows.

`PNil` is the empty program. It performs no operations, so its semantics is
`id`.

`PCons op p rest` adds the instruction `op` after a program whose semantics is `p`.
The resulting semantics is:
`execOpCode op . p`.

The type also checks that `p` produces enough stack elements for `op`.


Reasoning About Higher-Order Indices
------------------------------------

Now we can write a function that composes two stack programs.

\begin{code}
{-@ reflect compose @-}
{-@ compose :: s1:(Stack -> Stack) -> s2:(Stack -> Stack)
            -> Prop (Program s1) -> Prop (Program s2)
            -> Prop (Program (s2 . s1)) @-}
compose :: (Stack -> Stack) -> (Stack -> Stack) -> Program -> Program -> Program
compose s1 s2 p1 PNil                   = p1
compose s1 s2 p1 (PCons cmd srest rest) =
  PCons cmd (srest . s1) (compose s1 srest p1 rest)
\end{code}


The specification says that if `p1` has semantics `s1` and `p2` has semantics
`s2`, then `compose s1 s2 p1 p2` has semantics `s2 . s1`.

The verification requires reasoning about higher-order functions. 
In the `PNil` branch, we need to show that 

~~~~~{.spec}
Prop (Program s1) <: Prop (Program (s2 . s1))
~~~~~


To automate such higher order reasoning, 
the PLEX algorithm extends Liquid Haskell's PLE solver with beta, eta, unfolding, and local unification.

<div class="figure"
     id="fig:plex-algorithm"
     caption="Overview of the PLEX algorithm."
     file="img/PLEX.png"
     height="360px">
</div>

Assumptions 1-3 are introduced by the standard verification condition generation.
4 and 5 are $\eta$-expansions. 
6 and 8 are function unfolding and 7 is (dependent pattern matching) unification. 
Once all these steps are collected, 
SMT's congruence can easily discharge the goal.

In the PLEX paper, we show how higher order steps and 
dependent pattern matching are implemented in Liquid Haskell.



Arithmetic for Free: Completing the Compiler
------------------------------------------------

After `compose` is verified, 
we  define a correct by construction compiler.

The correctness is guaranteed by the type signature of compile,
which asserts that the semantics of the compiled program 
is equal to pushing on top ofthe stack the evaluation of 
the given expression.


\begin{code}
{-@ compile :: e:Expr -> Prop (Program (push $ eval e)) @-}
compile :: Expr -> Program
\end{code}

The implementation follows the expression structure.


\begin{code}
compile (EConst x)   = PCons (OpPush x) id PNil
compile (EAdd e1 e2) =
  PCons
    OpAdd
    ((push $ eval e1) . (push $ eval e2))
    (compose (push $ eval e2) (push $ eval e1) (compile e2) (compile e1))
compile (EMul e1 e2) =
  PCons
    OpMul
    ((push $ eval e1) . (push $ eval e2))
    (compose (push $ eval e2) (push $ eval e1) (compile e2) (compile e1))
compile (ENeg e)     =
  PCons
    OpMul
    ((push $ -1) . (push $ eval e))
    (PCons (OpPush $ -1) (push $ eval e) (compile e))    
\end{code}


The proof is very similar to the proof in Agda, 
but the SMT solver handles the arithmetic part. For example, in the `ENeg` case,
the compiler implements negation by multiplying by `-1`; the arithmetic proof
that `-a == a * (-1)` is discharged by SMT automation.


Summary
-------

We saw invariants on data types 
and how they naturally lead to data propositions.
Yet, data propositions can be used to encode semantic indices 
that, in turn, require higher-order reasoning.

PLEX permits higher order reasoning, integrated with SMT automation,
expanding the expressive power of refinement types; 
that can still be used to verify shallow properties of 
programs. 







\begin{code}
{-@ reflect id @-}
{-@ reflect $  @-}

{-@ reflect .  @-}
infixr 9 .
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)
\end{code}
