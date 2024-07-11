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
import Data.IORef
import System.Clock

%default total
```

## Purity and Side Effects

How does Idris implement computations with side effects such as
reading files, sending messages over the network, or showing an
animation on screen? All this can be done in a referentially
transparent way, by using a simple trick. But first, what does
it even mean for a function to be "referentially transparent"?

An expression is said to be "referentially transparent", if it
can be replaced with another expression denoting the same value, without
changing a program's behavior. Or, more simply put, a referentially
transparent expression can always be replaced with the value it
evaluates to without changing a program's behavior.

Let us look at an example:

```idris
square : Nat -> Nat
square x = x * x

eight : Nat
eight = square 2 + square 2
```

In the example above, we compute the same expression `square 2`
twice, which might be a waste of time if `square` were a long
running computation. Since `square` is referentially transparent -
the same argument will always lead to the same result - we (or the
compiler!) can rewrite `eight` in a more efficient way
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
  unsafePerformIO $ do
    v <- modifyIORef ref (+n)
    readIORef ref

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
changing a program's behavior. The reason for this is that
`callAndSum` reads and updates a mutable variable thus
changing its behavior whenever it is invoked several times with
the same mutable variable. This is
the opposite of referential transparency, and if the compiler
decided to convert `refNat1` to the form of `refNat2` as an
optimization, we would start to see different behavior probably
depending on the optimization level set at the compiler.

Note, however, that `refNat3` evaluates to the same value as
`refNat1`, and that's actually what this library is all about:
If we keep a mutable reference local to a computation, that is,
we create it and read and write to it as part of an isolate computation
without letting it leak out, that computation is still referentially
transparent, because the usage of a mutable reference is not
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
user input. How can that be referentially transparent.

Well, `IO a` is a wrapper around `PrimIO a`, and that is an alias
for `(1 w : %World) -> IORes a`. Now, what is that supposed to mean?
First, this value of type `%World` represents the current state
of the world: You computer's hard-drive, mouse position, the
temperature outside, number of babies currently filling their
diapers, everything: The whole universe. "How can that fit
into a single variable?", I hear you say. Well, it doesn't, nor
does it have to. `%World` is just a semantic token: It *represents*
the state of the world. It is important to note that it comes
at quantity one, so a function of type `IO a` must consume
the current state of the world exactly once. Afterwards, it
returns a value of type `IORes a`, which has a single
constructor `MkIORes` of type `a -> (1 w : %World) -> IORes a`.

And that's it! That's the whole magic of `IO`. Semantically, an
`IO` action consumes the current state of the world and returns
a result together with an *updated* state of the world. Since
no two world states are semantically the same, we can never
invoke an `IO` action with the same argument twice, so it
does not have to ever return the same result again.

Sounds like cheating? It is not. It actually works so well
and behaves exactly as expected, that huge effectful programs
can be safely built on top of this. But there is a caveat:
We are not supposed to have a value of type `%World`: It must
be provided by the runtime of our program when invoking the
`main` function. After that, the world state will be threaded
through the whole program, running all `IO` actions in sequence,
all of which will return an "updated" world that will be passed on
downstream.

We can actually look at how this works with an example:

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

In addition, we cannot ever break out of this `IO` stuff: Since every
`IO` action (remember, that's just a wrapper around `PrimIO`) returns
a new `%World` token of quantity one, we can't just drop the `%World`
token but have to pass it downstream, where it again needs to be
consumed exactly once. This means, that there is no legal way to
break out of `IO`, i.e. there is no function of type `IO a -> a`,
because such a function would not be referentially transparent
in general.

Of course, the code above is quite verbose compared to other imperative
languages (because that's what it is: imperative code!), so we define
a monad on top of all of this `IO` stuff, allowing us to sequence actions
nicely in in `do` blocks.

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

Sometimes we need to, especially when interacting with the foreign
function interface (FFI), where all guarantees are off anyway.
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

Assume, we'd like to pair every value of a container type
with an index representing the order at which it was
encountered. For lists, this is very simple, but not very
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

Now, that's quite a mouth full. And if we plan to statefully update
a tree in another way, we have to write all that again! Surely that's
not how things should be.

## A declarative and pure Solution: `traverse` and the `State` monad

Surely we can to better than that? We can. Note, how all
sub-computations in `zipWithIndexTree` end on function type
`Nat -> (Nat,a)` for different types `a`? We can abstract over
this function type and wrap it up in a new data constructor.
That's the `State` monad. And just like `IO a` is a monadic wrapper
for `PrimIO a`, `State s a` is a wrapper for `s -> (s,a)`. Note also,
how the code above with its `let`-bindings and pattern matches
on pairs, resembles the `PrimIO` code we wrote above. That's no
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

<!-- vi: filetype=idris2:syntax=markdown
-->
