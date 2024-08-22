# Linear mutable References and Utilities

Mutable state is anathema to pure functional programming.
Or is it? In this library, we explore a way to keep mutable
references and other mutable data structures
within the boundaries of pure computations, making sure they
do not leak into the outside world - and that they are properly released
before we are done. This allows us to get the raw performance - and sometimes,
convenience - of mutable state without sacrificing referential transparency.

Since we get automatic resource management with the approach
presented here, this can be used for many different kinds of (mutable)
resources the creation and manipulation of which does not have
a permanent observable effect: We can allocate (and release!) raw
C-pointers, mutable arrays, byte vectors, and hash maps; we can even setup
and tear down a full-fledged in-memory sqlite3 database without
resorting to `IO`! If we stretched the definition of what is an
"observable effect", we could even work with temporary files and
directories as long as we removed them all before we were done.
This adds quite a large subset of effectful computations to the list
of things that can be run and tested as pure functions, because all
mutable state is confined within the boundaries of these computations,
so that they are still referentially transparent when viewed from
the outside.

This is a literate Idris file, so we'll start with some imports.

```idris
module README

import Control.Monad.State
import Control.Monad.ST
import Data.IORef
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Derive.Prelude
import System.Clock

import Syntax.T1

%default total
%language ElabReflection
```

## What this Library offers

This is a small library providing a way to use mutable
references in pure code, using
a linear token to which the mutable references are bound via a parameter
to make sure all mutable state stays confined within the boundaries
of a pure computation.

An example (that could of course also be written with plain
tail-recursion in a much simpler way):

```idris
nextFibo : (r1,r2 : Ref1 Nat) -> F1' [r1,r2]
nextFibo r1 r2 t =
  let f1 # t := read1 r1 t
      f2 # t := read1 r2 t
      _  # t := write1 r2 (f1+f2) t
   in write1 r1 f2 t

fibo : Nat -> Nat
fibo n =
  run1 $ \t =>
    let A r2 t := ref1 (S Z) t
        A r1 t := ref1 (S Z) t
        _ #  t := forN n (nextFibo r1 r2) t
        v #  t := read1 r1 t
        _ #  t := release r1 t
        _ #  t := release r2 t
     in v # t
```

Or, with some syntactic sugar sprinkled on top:

```idris
fibo2 : Nat -> Nat
fibo2 n =
  allocRun1 [ref1 1, ref1 1] $ \[r1,r2] => T1.do
     forN n (nextFibo r1 r2)
     v <- read1 r1
     release r1
     release r2
     pure v
```

The techniques described in more detail below can also be used with
linear mutable arrays or byte vectors, which are often much harder to
replace in performance critical code than mere mutable references.

## Purity and Side Effects

How does Idris implement computations with side effects such as
reading files, sending messages over the network, or showing an
animation on screen? All this can be done in a referentially
transparent way by using a simple trick. But first, what does
it even mean for a function to be "referentially transparent"?

### (Breaking) Referential Transparency

An expression is said to be "referentially transparent", if it
can be replaced with another expression denoting the same value without
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
depending on the optimization level set at the compiler. Good
luck debugging this kind of wickedness!

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

Let's dissect this a bit.
First, this value of type `%World` represents the current state
of the world: You computer's hard-drive, mouse position, the
temperature outside, number of people currently having a drink,
everything: The whole universe. "How can that fit
into a single variable?", I hear you say. Well, it doesn't, nor
does it have to. `%World` is just a semantic token: It *represents*
the state of the world. At runtime, it is just a constant like `0`,
`null`, or `undefined` that's being passed around and never inspected.
It is only of importance at compile-time.

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
  Therefore, there cannot be a safe function of type `IO a -> a` that extracts
  a result from `IO`. This would require us to semantically destroy the
  world! Actually, there is `unsafePerformIO`, which has exactly this
  type. It is called "unsafe" for a reason.

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
by using utility `toPrim`. This is allowed and a safe thing to do. In
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
on pairs resembles the `PrimIO` code we wrote further above. That's no
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

And now it's a simple matter of traversing our data structures
with `pairWithIndex` and run the whole thing starting from
index zero:

```idris
zipWithIndexTreeState : Tree a -> Tree (Nat,a)
zipWithIndexTreeState = evalState 0 . traverse pairWithIndex

zipWithIndexListState : List a -> List (Nat,a)
zipWithIndexListState = evalState 0 . traverse pairWithIndex
```

Or, more general (this makes the two functions above redundant):

```idris
zipWithIndexState : Traversable f => f a -> f (Nat,a)
zipWithIndexState = evalState 0 . traverse pairWithIndex
```

Now that's more to our liking: Nice and declarative. And indeed,
the state monad together with traverse makes for a nice programming
experience.

### Performance Overhead

Monadic code in Idris currently comes with a considerable
overhead in performance: Zipping the values in a list with
their index is about ten times slower when using `traverse`
with `State` than with explicit recursion. In addition,
`traverse` cannot be made tail recursive unless it is
manually specialized for `State`, in which case we might
just as well ditch the `State` monad altogether. And
stack safety is important on all backends with a limited
stack size such as the JavaScript backends. There,
`zipWithIndexState` will overflow the call stack
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

The key idea to parameterize the `ST` monad
over a phantom type `s` (a type parameter with no runtime
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

In addition, it is currently not possible to get safe allocation-release
cycles (such as allocating and releasing the memory for a raw C-pointer)
with the `ST` monad. It is therefore quite limited in its current state.

## Enter: `T1`

I am now going to show how the limitations demonstrated above
can be overcome by using a linear token to which all kinds of
(mutable!) resources can be bound and use locally in a computation.

This is going to replace `ST s`, and comes without the overhead from
using a monad to sequence computations. The code therefore closely
resembles the raw let bindings of `PrimIO`. Here's the example for
zipping the values in a list with their index:

```idris
pairWithIndex1 : (r : Ref1 Nat) -> a -> (1 t : T1 [r]) -> R1 [r] (Nat,a)
pairWithIndex1 r v t =
  let n # t := read1 r t
      _ # t := write1 r (S n) t
   in (n,v) # t

zipWithIndex1 : Traversable1 f => f a -> f (Nat,a)
zipWithIndex1 as = withRef1 0 $ \r => traverse1 (pairWithIndex1 r) as
```

There are several things to note in the code above. First, `Ref1 Nat`
is a mutable reference holding a natural number. It is bound to a
linear token `t`, parameterized with a list of bound resources.
We cannot use a `Ref1 a` without the token it was bound to, and we cannot
bind it to a different token without using `unsafeBind`, which is again
called "unsafe" for a reason. Function `withRef1` allocates and releases
a mutable reference for us, and we are free to use it in our anonymous
function (after the dollar sign).

The type `(1 t : T1 rs) -> R1 rs a` is so common in this kind of computation,
that we get a short alias called `F1 rs a` for it:

```repl
README> :printdef F1
0 Data.Linear.Token.F1 : Resources -> Type -> Type
F1 rs a = T1 rs -@ R1 rs a
```

`R1 s a` is a linear result just like `IORes a`, that wraps a result
of type `a` with a new linear token of type `T1 rs`. All of this
allows us to write safe, single-threaded and stateful computations
in a way that strongly resembles programming in `PrimIO`.

But how does this prevent us from using functions such as `read1` or
`write1` with a mutable reference together with the wrong linear token?
When we look at the type of `read1`, we see that there is a link between
the mutable reference `r` and the list of resources `rs`:

```repl
README> :t read1
Data.Linear.Ref1.read1 : (r : Ref1 a) -> {auto 0 _ : Res r rs} -> F1 rs a
```

A value of type `Res r rs` is a proof that `r` is one of the elements of `rs`,
that is, `r` is one of the resources bound to the linear token! Since a
mutable reference will always be bound to the linear token it was created with
(see function `ref1`), it is not possible to use a mutable reference with
the wrong token. It therefore becomes completely useless outside of the
current linear computation.

### A simple Word Count Example

In order to demonstrate how all of this works together, we are
going to write a simple word count program that counts characters,
words, and lines of text in a single traversal of a list of
characters. I'm not claiming that this is the most elegant or
declarative way to do this. It just shows how to create, use, and
release mutable references.

When counting characters, words, and lines, we need three
mutable references for counting each entity. In addition, we
need a boolean flag to keep track of word beginnings and ends.

With these, we can write a couple of utilities and then the
main character processing routine. Their result type is
always `F1' rs`, which is an alias for `(1 t : T1 rs) -> T1 rs`.
So, these are functions that potentially mutate some state but
do not produce any other results of interest.

```idris
inc : (r : Ref1 Nat) -> (0 p : Res r rs) => F1' rs
inc r = mod1 r S

endWord : (b : Ref1 Bool) -> (w : Ref1 Nat) -> F1' [c,w,l,b]
endWord b w t =
  let _ # t := whenRef1 b (inc w) t
   in write1 b False t

processChar : (c,w,l : Ref1 Nat) -> (b : Ref1 Bool) -> Char -> F1' [c,w,l,b]
processChar c w l b x t =
  case isAlpha x of
    True  =>
      let _ # t := write1 b True t
       in inc c t
    False =>
      let _ # t := when1 (x == '\n') (inc l) t
          _ # t := endWord b w t
       in inc c t
```

The actual `wordCount` function has to setup all mutable variables,
traverse the sequence of characters, read the final values from
the mutable refs, and cleanup everything at the end.

```idris
record WordCount where
  constructor WC
  chars : Nat
  words : Nat
  lines : Nat

%runElab derive "WordCount" [Show,Eq]

wordCount : String -> WordCount
wordCount "" = WC 0 0 0
wordCount s  =
  run1 $ \t =>
    let A b t  := ref1 False t
        A l t  := ref1 (S Z) t
        A w t  := ref1 Z t
        A c t  := ref1 Z t
        _ # t  := traverse1_ (processChar c w l b) (unpack s) t
        _ # t  := endWord b w t
        x  # t := readAndRelease c t
        y  # t := readAndRelease w t
        z  # t := readAndRelease l t
        _  # t := release b t
     in WC x y z # t
```

This last step is quite verbose. This is to be expected: Just like in
imperative languages, we have to introduce mutable variables before
we can use them. It is also a bit tedious that we have to manually
thread our linear token through the whole computation. There is
some `do` and applicative notation available from `Syntax.T1`,
but it does not yet work with resource allocation. However, there is
also utility function `allocRun1`, which allows us to allocate
all resources from a heterogeneous list in one go.
Here's the word count example with some syntactic sugar:

```idris
wordCount2 : String -> WordCount
wordCount2 "" = WC 0 0 0
wordCount2 s  =
  allocRun1 [ref1 0,ref1 0,ref1 1,ref1 False] $ \[c,w,l,b] => T1.do
    traverse1_ (processChar c w l b) (unpack s)
    endWord b w
    release b
    x <- readAndRelease c
    y <- readAndRelease w
    z <- readAndRelease l
    pure $ WC x y z
```

Even though syntax is not yet perfect,
we gain a lot from all of this: Fast, mutable state localised
to pure computations together with safe resource management.
To understand this, look at the type of `run1`:

```repl
README> :t run1
Data.Linear.Token.run1 : F1 [] a -> a
```

We extract a value of type `a` from a linear computation that
*starts and ends* with zero allocated resources: We can't forget to
release all resources that we set up along the way!

Finally, we can test our mini application:

```idris
covering
main : IO ()
main = do
  printLn (wordCount "hello world!\nhow are you?")
  printLn (wordCount2 "hello world!\nhow are you?")
```

<!-- vi: filetype=idris2:syntax=markdown
-->
