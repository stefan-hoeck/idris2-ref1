# Linear mutable References and Utilities

Mutable state is anathema to pure functional programming.
Or is it? In this library, we explore a way to keep mutable
references and other mutable data structures
within the boundaries of pure computations, making sure they
do not leak into the outside world. This allows us to get
the raw performance - and sometimes, convenience - of mutable state
without sacrificing referential transparency.

This is a literate Idris file, so we'll start with some
imports.

```idris
module README

import Control.Monad.State
import Control.Monad.ST
import Data.IORef
import Data.Linear.Ref1
import Data.Linear.Token.Syntax
import Data.Linear.Traverse1
import Derive.Prelude
import System.Clock

%default total
%language ElabReflection
```

## What this Library offers

This is a small library providing a way to use mutable
references as auto-implicit arguments in pure code, using
a linear token bound via a parameter to the mutable references
to make sure all mutable state stays confined within the boundaries
of a pure computation.

An example (that could of course also be written with plain
tail-recursion in a much simpler way):

```idris
data Fibo = V1 | V2

nextFibo : Ref1 V1 s Nat => Ref1 V2 s Nat => F1' s
nextFibo t0 =
  let f1 # t1 := read1At V1 t0
      f2 # t2 := read1At V2 t1
   in write1At V1 f2 (write1At V2 (f1+f2) t2)

fibo : Nat -> Nat
fibo n =
  run1 $ Token.Syntax.do
    r1 <- ref1At V1 1
    r2 <- ref1At V2 1
    forN n nextFibo
    read1At V1
```

The techniques described in more detail below can also be used with
linear mutable arrays or byte vectors, which are often much harder to
replace in performance critical code than mere mutable references.

## Purity and Side Effects

How does Idris implement computations with side effects such as
reading files, sending messages over the network, or showing an
animation on screen? All this can be done in a referentially
transparent way, by using a simple trick. But first, what does
it even mean for a function to be "referentially transparent"?

### (Breaking) Referential Transparency

An expression is said to be "referentially transparent", if it
can be replaced with another expression denoting the same value, without
changing a program's behavior. Or, more simply put, a referentially
transparent expression can always be replaced with the value it
evaluates to without changing a program's behavior.

Let's look at an example:

```idris
square : Nat -> Nat
square x = x * x

eight : Nat
eight = square 2 + square 2
```

In the example above, we compute the same expression `square 2`
twice, which might be a waste of time if `square` were a long
running computation. Since `square` is referentially transparent -
calling it with the same argument will always lead to the same
result - we (or the compiler!) can rewrite `eight` in a more efficient way
by storing the result of evaluating `square 2` in a variable:

```idris
eight2 : Nat
eight2 = let s := square 2 in s + s
```

Now, let us come up with something that is not referentially
transparent (don't do this!):

```idris
-- create a new mutable reference outside of `IO`:
-- don't do this!
mkRef : Nat -> IORef Nat
mkRef = unsafePerformIO . newIORef

-- read and write to a mutable reference outside
-- of `IO`: don't do this!
callAndSum : IORef Nat -> Nat -> Nat
callAndSum ref n =
  unsafePerformIO $ modifyIORef ref (+n) >> readIORef ref

refNat1 : Nat
refNat1 = callAndSum (mkRef 0) 10 + callAndSum (mkRef 0) 10

refNat2 : Nat
refNat2 =
  let ref := mkRef 0
   in callAndSum ref 10 + callAndSum ref 10

refNat3 : Nat
refNat3 =
  let x := callAndSum (mkRef 0) 10
   in x + x
```

If you checkout the values of `refNat1` and `refNat2` at the
REPL (by invoking `:exec printLn refNat1`), you will note
that they are not the same. Obviously, we can't just replace
`mkRef 0` with the value it evaluates to without
changing the program's behavior. The reason for this is that
`callAndSum` reads and updates a mutable variable thus
changing its behavior whenever it is invoked several times with
the same mutable variable. This is
the opposite of referential transparency, and if the compiler
decided to convert `refNat1` to the form of `refNat2` as an
optimization, we would start seeing different behavior probably
depending on the optimization level set at the compiler.

Note however, that `refNat3` evaluates to the same value as
`refNat1`, and that's actually what this library is all about:
If we keep a mutable reference local to a computation, that is,
we create it and read and write to it as part of an isolate computation
without letting it leak out, that computation is still referentially
transparent, because the usage of the mutable reference is not
observable from the outside. The problem with `refNat2` is
that we pass *the same reference* around, so that it can freely be
mutated during or between function calls. This makes the result
of a function invocation dependent on the reference's current state,
and that's what's breaking referential transparency.

To recap: In the examples above `callAndSum (mkRef x) y` is a
referentially transparent expression for all `x` and `y`,
while `callAndSum ref x` is not.

### But what about `IO`?

Yes, we need to talk about how `IO` works under the hood and
how it upholds referential transparency. Obviously, a
function such as `getLine` (of type `IO String`) yields
a different result every time it is run depending on
user input. How can that be referentially transparent?

Well, `IO a` is a wrapper around `PrimIO a`, and that is an alias
for the following:

```repl
Main> :printdef PrimIO
PrimIO.PrimIO : Type -> Type
PrimIO a = (1 _ : %World) -> IORes a
```

Now, what is that supposed to mean?
First, this value of type `%World` represents the current state
of the world: You computer's hard-drive, mouse position, the
temperature outside, number of people currently having a drink,
everything: The whole universe. "How can that fit
into a single variable?", I hear you say. Well, it doesn't, nor
does it have to. `%World` is just a semantic token: It *represents*
the state of the world. At runtime, it is just a constant like `0`,
`null`, or `undefined` that's being passed around. It is only of
importance at compile-time.

It is important to note that `%World` comes
at quantity one, so a function of type `IO a` must consume
the current state of the world exactly once. Afterwards, it
returns a value of type `IORes a`, which has a single
constructor:

```repl
Main> :doc IORes
data PrimIO.IORes : Type -> Type
  Totality: total
  Visibility: public export
  Constructor: MkIORes : a -> (1 _ : %World) -> IORes a
```

And that's it! That's the whole magic of `IO`. Semantically, an
`IO a` action consumes the current state of the world and returns
a result of type `a` together with an *updated* state of the world.
Since no two world states are semantically the same, we can never
invoke an `IO` action with the same argument twice, so it
does not have to ever return the same result again and still upholds
referential transparency.

Sounds like cheating? It is not. It actually works so well
and behaves exactly as expected that huge effectful programs
can be safely built on top of this. But there are some caveats:

* We are not supposed to have a value of type `%World`: It must
  be provided by the runtime of our program when invoking the
  `main` function. After that, the world state will be threaded
  through the whole program, running all `IO` actions in sequence,
  each returning an "updated" world that will be passed on
  downstream.
* Since the world state is never ever the same again, it can be hard to
  test `IO` actions in a reproducible way. They are free to produce
  random results (of the correct type!) after all.
* Once we are passing around the world state, we can't stop doing so, that
  is, we can't break out of `IO`. We always have a world state of
  quantity one, so we must consume it, but as soon as it has been consumed,
  we get another one, again of quantity one.
  So, there cannot be a safe function of type `IO a -> a` that extracts
  a result from `IO`. This would require us to semantically destroy the
  world! Actually, there is `unsafePerformIO`, which has exactly this
  type, and it is called "unsafe" for a reason.

We can look at how all of this works with an example:

```idris
printTimePrim : PrimIO ()
printTimePrim w1 =
  let MkIORes t1 w2 := toPrim (clockTime UTC) w1
      MkIORes () w3 := toPrim (putStrLn "The current time is: ") w2
      MkIORes () w4 := toPrim (printLn t1) w3
      MkIORes t2 w5 := toPrim (clockTime UTC) w4
      MkIORes () w6 := toPrim (putStrLn "Now the time is: ") w5
   in toPrim (printLn t2) w6

printTime : IO ()
printTime = primIO printTimePrim
```

In the code above, we converted all `IO` actions to `PrimIO` functions
by using utility `toPrim`. This is allowed and a safe thing to do! In
`PrimIO`, we run computations with side effects by passing around
the `%World` token explicitly (starting with `w1`). Every effectful
computation will consume the current world state, and - since it has
linear quantity - we will not be able to ever use it again. Instead,
we get a new value of type `%World` (again at quantity one) wrapped
up in an `IORes`: The "updated" world state. Therefore, it is perfectly
fine that the two calls to `clockTime UTC` (they read the current system
clock) do not return the same time: They are invoked with distinct
world tokens (`w1` and `w4`, respectively).

Of course, the code above is quite verbose compared to other imperative
languages (because that's what it is: imperative code!), so we define
a monad on top of all of this `IO` stuff, allowing us to sequence actions
nicely in `do` blocks.

```idris
printTimeIO : IO ()
printTimeIO = do
  t1 <- clockTime UTC
  putStrLn "The current time is: "
  printLn t1
  t2 <- clockTime UTC
  putStrLn "Now the time is: "
  printLn t2
```

To sum this up: Every evaluation of an `IO` action consumes the
current world state, and we can't reuse it, nor will we ever get it back.
Therefore - by design - an `IO` action *can't* be invoked with the same
arguments twice, and so it does not have to ever return the same
result in a predictable manner.

### But can't we cheat?

Sometimes we have to, especially when interacting with the foreign
function interface (FFI) where all guarantees are off anyway.
Therefore, `%MkWorld` is a value of type `%World` that's available
to us, and we can theoretically destroy (consume) a value of this
type by pattern-matching on it. This allows us
to implement functions such as `unsafePerformIO` in the Prelude.
But we must never do that unless we know exactly why we are
doing it and what the consequences are.

## Stateful Computations

A special case of computations with side effects are those that
read and update mutable state. Before we are going to look
at how to work safely with proper mutable references, we are
going to look at some pure alternatives.

Let's assume we'd like to pair every value of a container type
with an index representing the order at which it was
encountered. For lists, this is very simple but not very
pretty:

```idris
zipWithIndexList : List a -> List (Nat,a)
zipWithIndexList = go 0
  where
    go : Nat -> List a -> List (Nat,a)
    go n []      = []
    go n (x::xs) = (n,x) :: go (S n) xs
```

As you can see, we thread the changing state (the current index,
represented by a natural number) through the computation, updating
it on every recursive call. This works nicely and is OK to read
although we use explicit recursion.

Let's try something a bit more involved: Pairing the values
in a rose tree with their index:

```idris
data Tree : Type -> Type where
  Leaf : (val : a) -> Tree a
  Node : List (Tree a) -> Tree a

%runElab derive "Tree" [Show,Eq]
```

In order to zip a tree's values with their index, we need to be
a bit more creative: We not only return the updated tree
on every recursive call but also the last index encountered:

```idris
zipWithIndexTree : Tree a -> Tree (Nat, a)
zipWithIndexTree t = snd $ go t 0
  where
    go : Tree a -> Nat -> (Nat,Tree (Nat,a))

    many : List (Tree a) -> Nat -> (Nat,List (Tree (Nat,a)))
    many []        k = (k,[])
    many (x :: xs) k =
      let (k2,y)  := go x k
          (k3,ys) := many xs k2
       in (k3,y::ys)

    go (Leaf v)  n = (S n, Leaf (n,v))
    go (Node ts) n = let (n2,ts) := many ts n in (n2,Node ts)
```

Now, that's quite a mouthful. And if we plan to statefully update
a tree in another way, we have to write all that or something similar
again! Surely that's not how things should be.

## A declarative and pure Solution: `traverse` and the `State` monad

Surely we can to better than that? We can. Note, how all
sub-computations in `zipWithIndexTree` end on function type
`Nat -> (Nat,a)` for different types `a`? We can abstract over
this function type and wrap it up in a new data constructor.
That's the `State` monad. And just like `IO a` is a monadic wrapper
for `PrimIO a`, `State s a` is a wrapper for `s -> (s,a)`. Note also,
how the code with its `let`-bindings and pattern matches
on pairs, resembles the `PrimIO` code we wrote further above. That's no
coincidence: Both describe pure, stateful computations after all.

Now, I'm not going to look at the state monad in detail, but I'll
show how it can be used to convert ugly explicit recursion
into declarative code. First, the stateful computation that pairs a
value with the current index and increases the
index by one afterwards:

```idris
pairWithIndex : a -> State Nat (Nat,a)
pairWithIndex v = do
  x <- get
  put (S x)
  pure (x,v)
```

Next, an applicative tree traversal: This describes the recursive
traversal once and for all. First, we need to implement some
interfaces. To keep this short, I'm going to use `assert_total`:

```idris
export
Functor Tree where
  map f (Leaf v) = Leaf (f v)
  map f (Node xs) = assert_total $ Node (map (map f) xs)

export
Foldable Tree where
  foldr f v (Leaf x) = f x v
  foldr f v (Node xs) = assert_total $ foldr (flip $ foldr f) v xs

export
Traversable Tree where
  traverse g (Leaf val) = Leaf <$> g val
  traverse g (Node xs)  =
    assert_total (Node <$> traverse (traverse g) xs)
```

And now it's a simple matter to traverse our data structures
with `pairWithIndex` and run the whole thing starting from
index zero:

```idris
zipWithIndexTreeState : Tree a -> Tree (Nat,a)
zipWithIndexTreeState = evalState 0 . traverse pairWithIndex

zipWithIndexListState : List a -> List (Nat,a)
zipWithIndexListState = evalState 0 . traverse pairWithIndex
```

Now that's more to our liking: Nice and declarative. And indeed,
the state monad together with traverse makes for a nice user
experience.

### Performance Overhead

Monadic code in Idris currently comes with a considerable
overhead in performance: Zipping the values in a list with
their index is about ten times slower when using `traverse`
with `State` than with explicit recursion. In addition,
`traverse` cannot be made tail recursive unless it is
manually specialized for `State`, in which case we might
just as well ditch the `State` monad altogether. And
stack safety is important on all backends with a limted
stack size such as the JavaScript backends. There,
`zipWithIndexListState` will overflow the call stack
for lists holding more than a couple of thousand elements.

So, with the above two options it seems like we either get
raw performance but have to write explicit recursions,
which is not exactly declarative programming, or we
lose in terms of performance and stack safety when using
powerful declarative tools such as `traverse`.

### The `ST` Monad

As an alternative to the `State` monad, the `ST` monad
(from `Control.Monad.ST`) offers true mutable state
localized to pure stateful computations. It is based on
Haskell's [Lazy Functional State Threads](https://www.microsoft.com/en-us/research/wp-content/uploads/1994/06/lazy-functional-state-threads.pdf),
which offers safe encapsulation of mutable state
in pure, referentially transparent computations.

The key idea is, that the `ST` monad is parameterized
by a phantom type (a type parameter with no runtime
relevance): `ST s a`. Mutable arrays and references are
then parameterized by the same phantom type `s`, so
that a mutable reference invariably belongs to a specific,
single-threaded computation. For instance:

```idris
pairWithIndexST : STRef s Nat -> a -> ST s (Nat,a)
pairWithIndexST ref v = do
  x <- readSTRef ref
  writeSTRef ref (S x)
  pure (x,v)

zipWithIndexST : Traversable f => f a -> f (Nat,a)
zipWithIndexST t =
  runST $ newSTRef 0 >>= \ref => traverse (pairWithIndexST ref) t
```

The code looks similar to what a traversal with `State` offers,
but it uses a proper mutable reference internally and thus
performs about twice as fast as the version with the state monad.

However, in order to make this safe, great care must be taken to
not leak any mutable state into the outside world. To guarantee this,
function `runST` only accepts computations that are universally
quantified over `s`: Such a function can never leak a mutable
reference, because the reference would be bound to a concrete
state thread and thus, to a concrete phantom type `s`. That's
a type error. It is also not possible to smuggle out a mutable
reference in an existential type and still use it at a later time.
For that to work, we'd have to show that the tag of the current
state thread is the same as the one of the mutable reference.
Since `s` is erased, we have no way of comparing two such
tags. Let's quickly look at both types of safety guard.

In the following example, we try to leak out a mutable reference
to the outside world in order to (unsafely!) use it in a later
computation:

```idris
failing
  leak1 : STRef s Nat
  leak1 = runST (newSTRef 1)
```

As you can see, this does not work. We cannot get something tagged with
phantom type `s` out of an `ST` computation. Changing `s` to something
different does also not work: It is still universally quantified in `runST`:

```idris
failing
  leak2 : STRef () Nat
  leak2 = runST (newSTRef 1)
```

In the next example, we try to trick Idris into leaking an existentially
typed reference:

```idris
record ExRef a where
  constructor ER
  {0 state : Type}
  ref : STRef state a

leak3 : ExRef Nat
leak3 = runST (ER <$> newSTRef 1)
```

It works! Ha, now we are going to do some evil stuff!

```idris
failing
  useExRef : ExRef a -> ST s ()
  useExRef (ER ref) = writeSTRef ref 10
```

Doh. Idris does not accept this because `state` does not unify with `s`.
These last examples should demonstrate that it is indeed safe to use mutable
references (and also arrays) within the `ST` monad, because even if we
manage to get them out of `ST`, they can no longer be used at all.

And yet, `ST` is still considerably slower than explicit recursion.
In addition, `traverse` is still not stack-safe, so it can't be used
with large lists on the JavaScript and similar backends.

## Enter: `Ref1`

I am now going to show how the limitations demonstrated above
can be overcome by using mutable references tagged in a similar way
as `STRef` but bound to a linear token with the same tag that
guarantees the computation stays in the same computational thread.

This is going to replace `ST s`, and comes without the overhead from
using a monad to sequence computations. The code therefore closely
resembles the raw let bindings of `PrimIO`. Here's the example for
zipping the values in a list with their index:

```idris
pairWithIndex1 : Ref1 () s Nat => a -> F1 s (Nat, a)
pairWithIndex1 v t1 =
  let n # t2 := read1 t1
   in (n,v) # write1 (S n) t2

zipWithIndex1 : Traversable1 f => f a -> f (Nat,a)
zipWithIndex1 as = withRef1 0 (traverse1 pairWithIndex1 as)
```

There are several things to note in the code above. First, `Ref1 () s Nat`
is a mutable reference holding a natural number. It is parameterized over
the state thread `s` just like `STRef` in the `ST` monad. However, `Ref1`
comes with another parameter, set to unit (`()`) in the example above.

The idea is to use mutable references as auto-implicit arguments. This
allows us to conveniently put them in `parameters` blocks thus
decluttering our function signatures. But then it can be tedious to
distinguish between mutable references if several of them are
currently in use. For these occasions, we can tag them with
something more specific than unit and use functions such as
`read1At` and `write1At` together with a reference's tag to specify
exactly, which tag we mean.

Second, the result type of `pairWithIndex1` is `F1 s (Nat,a)`, which
is function alias just like `PrimIO a`:

```repl
README> :printdef F1
0 Data.Linear.Token.F1 : Type -> Type -> Type
F1 s a = T1 s -@ R1 s a
```

This shows us two more ingredients: `T1 s` and `R1 s a`.
`T1 s` is a linear token comparable to `%World` because
it must be used exactly once to avoid calling a function
with mutable state with the same arguments twice. Unlike `%World`,
we are allowed to create (see below) and destroy (`discard`) such
tokens at will, thus using them to write pure functions that use
mutable state under the hood.

`R1 s a` is a linear result just like `IORes a`, that wraps a result
of type `a` with a new linear token of type `T1 s`. All of this
allows us to write safe, single-threaded and stateful computations
in a way that strongly resembles programming in `PrimIO`.

### A simple Word Count Example

In order to demonstrate the use of tagged references, we are
going to write a simple word count program that counts characters,
words, and lines of text in a single traversal of a list of
characters. I'm not claiming that this is the most elegant or
declarative way to do this. It just shows how to use tags.

When counting characters, words, and lines, we need three
mutable references for counting each entity. In addition, we
need a boolean flag to keep track of word beginnings and ends.

We can define an enum type for these four references:

```idris
data Tag = Chars | Words | Lines | InWord
```

With these, we can write a couple of utilities and then the
main character processing routine. Their result type is
always `F1' s`, which is an alias for `(1 t : T1 s) -> T1 s`.
So, this is a function that potentially mutates some state but
does not produce any other result of interest.

```idris
inc : (0 tag : _) -> Ref1 tag s Nat => F1' s
inc tag = mod1At tag S

endWord : Ref1 InWord s Bool => Ref1 Words s Nat => F1' s
endWord t = write1At InWord False (whenRef1 InWord (inc Words) t)

parameters {auto cs : Ref1 Chars s Nat}
           {auto ws : Ref1 Words s Nat}
           {auto ls : Ref1 Lines s Nat}
           {auto iw : Ref1 InWord s Bool}

  processChar : Char -> F1' s
  processChar c t =
    case isAlpha c of
      True  => inc Chars (write1At InWord True t)
      False => inc Chars $ endWord $ when1 (c == '\n') (inc Lines) t
```

The actual `wordCount` function has to setup all mutable variables,
traverse the sequence of characters, and read the final values from
the mutable refs.

```idris
record WordCount where
  constructor WC
  chars : Nat
  words : Nat
  lines : Nat

%runElab derive "WordCount" [Show,Eq]

wordCount1 : String -> WordCount
wordCount1 "" = WC 0 0 0
wordCount1 s  =
  run1 $ \t1 =>
    let cs # t2  := ref1At Chars Z t1
        ws # t3  := ref1At Words Z t2
        ls # t4  := ref1At Lines (S Z) t3
        iw # t5  := ref1At InWord False t4
        t6       := traverse1_ processChar (unpack s) t5
        t7       := endWord t6
        x  # t8  := read1At Chars t7
        y  # t9  := read1At Words t8
        z  # t10 := read1At Lines t9
     in WC x y z # t10
```

This last step is quite verbose. Since this is not a performance-critical
part of our code (the machinery has to be set up only once in order
to process potentially huge amounts of text), we can opt for some
syntactic sugar (from module `Data.Linear.Token.Syntax`):

```idris
wordCount : String -> WordCount
wordCount "" = WC 0 0 0
wordCount s  =
  run1 $ Token.Syntax.do
    cs <- ref1At Chars Z
    ws <- ref1At Words Z
    ls <- ref1At Lines (S Z)
    iw <- ref1At InWord False
    traverse1_ processChar (unpack s)
    endWord
    [| WC (read1At Chars) (read1At Words) (read1At Lines) |]

main : IO ()
main = do
  printLn (wordCount1 "hello world!\nhow are you?")
  printLn (wordCount "hello world!\nhow are you?")
```

That's quite a bit more concise. We used qualified `do` notation, because
`F1 s` is not a proper monad. Note, however, that this second version of `wordCount`,
generates quite a bit more code that's also significantly slower, so avoid doing
this in performance-critical parts of your code.

<!-- vi: filetype=idris2:syntax=markdown
-->
