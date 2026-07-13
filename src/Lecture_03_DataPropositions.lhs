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

{-@ reflect id @-}
{-@ reflect $  @-}
{-@ infix $    @-}

{-@ reflect .  @-}
{-@ infix .    @-}
infixr 9 .
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)
\end{code}


In this last part, we explore the expresivity of refinement types. 
The two main limitations are 

1. the encoding of inductive data types, and

2. the reasoning about higher-order functions.

The example of this lecture is based on 
the [PLEX paper](https://dl.acm.org/doi/epdf/10.1145/3798248) and collects 
all the steps which with Liquid Haskell's solver extends the SMT logic. 


The goal is to explain the
running example: [a correct-by-construction compiler](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/calculating-correct-compilers/70AA17724EBCA4182B1B2B522362A9AF?utm_campaign=shareaholic&utm_medium=copy_link&utm_source=bookmark) from arithmetic
expressions to a stack machine.



Refinement Types: Calculating Correct Compilers
---------------------------------------------------

We start with a small expression language.

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


The `reflect` annotation is what connects the Haskell definition to the logic.
When Liquid Haskell sees it, it:

1. creates a logical symbol for `eval`;
2. checks that `eval` terminates;
3. gives the definition of `eval` to PLE.

So later, when a refinement mentions `eval (EAdd e1 e2)`, PLE can unfold it to
`eval e1 + eval e2`, and the SMT solver can reason about the arithmetic.


The Stack Machine
-----------------

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

Concretely:

\begin{code}
data PROGRAM = Program (Stack -> Stack)
\end{code}


The index is a function from stacks to stacks. A value of type `Program p`
represents a program whose semantics is the stack transformer `p`.

Liquid Haskell encodes such indexed values with data propositions:

\begin{code}

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

\end{code}

Using data propositions, we give the program constructors the following
shape:

\begin{code}

data Program where
{-@ PNil :: Prop (Program id) @-}
  PNil :: Program
{-@ PCons :: op:OpCode
          -> p:(Stack -> { v:Stack | len v >= minStackSize op }) -> Prop (Program p)
          -> Prop (Program (execOpCode op . p)) @-}
  PCons :: OpCode -> (Stack -> Stack) -> Program -> Program


\end{code}

Read the constructors as follows.

`PNil` is the empty program. It performs no operations, so its semantics is
`id`.

`PCons op p rest` adds instruction `op` after a program whose semantics is `p`.
The resulting semantics is:

~~~~~{.spec}
execOpCode op . p
~~~~~

The type also checks that `p` produces enough stack elements for `op`.


Reasoning About Higher-Order Indices
------------------------------------

Now we can write a function that composes two stack programs.

\begin{code}
{-@ reflect compose @-}
{-@ compose :: p1:(Stack -> Stack) -> p2:(Stack -> Stack)
            -> Prop (Program p1) -> Prop (Program p2)
            -> Prop (Program (p2 . p1)) @-}
compose :: (Stack -> Stack) -> (Stack -> Stack) -> Program -> Program -> Program
compose s1 s2 p1 PNil                   = p1
compose s1 s2 p1 (PCons cmd srest rest) =
  PCons cmd (srest . s1) (compose s1 srest p1 rest)
\end{code}


The specification says that if `p1` has semantics `s1` and `p2` has semantics
`s2`, then `compose s1 s2 p1 p2` has semantics `s2 . s1`.

This is where vanilla PLE gets stuck. The proof is not just about unfolding
recursive functions. It needs reasoning about functions as values.


The PNil Branch
---------------

The interesting case is the `PNil` branch:

~~~~~{.spec}
compose s1 s2 p1 PNil = p1
~~~~~

The expected result type is:

~~~~~{.spec}
Prop (Program (s2 . s1))
~~~~~

But the returned expression `p1` has type:

~~~~~{.spec}
Prop (Program s1)
~~~~~

Why is this okay? Because in the `PNil` branch, pattern matching tells us that
`p2` is the empty program. Since `p2` was assumed to have semantics `s2`, and
`PNil` has semantics `id`, we learn locally:

~~~~~{.spec}
s2 == id
~~~~~

So the target semantics:

~~~~~{.spec}
s2 . s1
~~~~~

should simplify to:

~~~~~{.spec}
id . s1 == s1
~~~~~

Therefore `p1` is exactly the right result. The problem is that this reasoning
uses higher-order equality and a local equality learned from pattern matching.
A first-order SMT solver does not do this by itself.


The PLEX Algorithm
----------------------

Next we explain how PLEX proves the `PNil` branch.

The subtyping goal is:

~~~~~{.spec}
Prop (Program s1) <: Prop (Program (s2 . s1))
~~~~~

under the local facts produced by the branch:

~~~~~{.spec}
prop p1 == Program s1
prop p2 == Program s2
prop p2 == Program id
~~~~~

The SMT solver can see that `s2` and `id` are related through the equalities
about `prop p2`, but it still cannot conclude that `s2 . s1` is the same
function as `s1`.

PLEX adds the missing higher-order normalization steps.


Step 1: Eta and Beta Equalities
-------------------------------

PLEX eta-expands functions so they can be compared by their behavior on an
argument.

For example:

~~~~~{.spec}
s1       == \x -> s1 x
s2 . s1  == \x -> (s2 . s1) x
~~~~~

This turns function equality into equality of fully applied terms.

PLEX also supports beta reduction:

~~~~~{.spec}
(\x -> e) y == e[y/x]
~~~~~

These equalities are not added as unsafe axioms. PLEX introduces them in a
typed and controlled way, so the generated terms respect refinements.


Step 2: Function Unfolding
--------------------------

Once the composed function is applied to an argument, PLE-style unfolding can
expand function composition:

~~~~~{.spec}
(s2 . s1) x == s2 (s1 x)
~~~~~

This is the point where ordinary PLE and the new higher-order reasoning work
together. Eta expansion creates the fully applied term, and unfolding simplifies
that term.


Step 3: Unification from Pattern Matching
-----------------------------------------

In the `PNil` branch, pattern matching gives us:

~~~~~{.spec}
prop p2 == Program s2
prop p2 == Program id
~~~~~

Since the `Program` constructor is injective, PLEX can learn the local unifier:

~~~~~{.spec}
s2 == id
~~~~~

Then it can rewrite:

~~~~~{.spec}
s2 (s1 x) == id (s1 x)
~~~~~

This equality is local to the branch. PLEX records such equalities in a delta
environment.


Step 4: Completing the Branch
-----------------------------

Finally, PLEX unfolds `id`:

~~~~~{.spec}
id (s1 x) == s1 x
~~~~~

Putting the equalities together:

~~~~~{.spec}
(s2 . s1) x
== s2 (s1 x)
== id (s1 x)
== s1 x
~~~~~

So:

~~~~~{.spec}
s2 . s1 == s1
~~~~~

and therefore:

~~~~~{.spec}
Prop (Program s1) <: Prop (Program (s2 . s1))
~~~~~

The `PNil` branch verifies.

The inductive `PCons` branch follows the same idea, but with one more layer of
composition. PLEX again combines eta expansion, beta reduction, unfolding, and
local unification.


Arithmetic for Free: Completing the Compiler
------------------------------------------------

After `compose` is verified, we can define the compiler so that correctness is
guaranteed by its type.

The intended type is:

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


This compiler is correct by construction. Each branch returns a `Program` whose
semantic index is exactly `push (eval e)`.

PLEX handles the higher-order part:

* composition of stack transformers;
* eta expansion of partially applied functions;
* beta reduction of lambdas;
* unification from pattern matching on data propositions.

The SMT solver handles the arithmetic part. For example, in the `ENeg` case,
the compiler implements negation by multiplying by `-1`; the arithmetic proof
that `-a == a * (-1)` is discharged by SMT automation.


Summary
-------

We show the complete steps of the PLEX algorithm, 
which extends Liquid Haskell's solver  with higher-order reasoning. Concretely,

1. We want a correct-by-construction compiler.
2. Correctness is encoded in the type of stack-machine programs.
3. Program types are indexed by functions from stacks to stacks.
4. Composition of programs requires higher-order reasoning.
5. Vanilla PLE unfolds functions, but does not reason enough about functions as
   values.
6. PLEX adds beta, eta, unfolding, and local unification.
7. After that normalization, SMT can finish the remaining first-order goals.

