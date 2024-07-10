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
compiler!) can implement `eight` in a more efficient way
by storing the result of evaluating `square 2` in a variable:

```idris
eight2 : Nat
eight2 = let s := square 2 in s + s
```

Now, let us come up with something that is not referentially
transparent (don't do this!):

```idris
mkRef : Nat -> IORef Nat
mkRef = unsafePerformIO . newIORef

callAndSum : IORef Nat -> Nat -> Nat
callAndSum ref n =
  unsafePerformIO $ do
    v <- modifyIORef ref (+n)
    readIORef ref

refNat1 : Nat
refNat1 =
  let ref := mkRef 0
   in callAndSum ref 10 + callAndSum ref 10

refNat2 : Nat
refNat2 =
  let ref := mkRef 0
      x   := callAndSum ref 10
   in x + x
```

If you checkout the values of `refNat1` and `refNat2` at the
REPL (by invoking `:exec printLn refNat1`), you will note
that they are not the same. Obviously, we can't just replace
`callAndSum ref 10` with the value it evaluates to without
changing a program's behavior. The reason for this is that
`callAndSum` reads and updates a mutable variable, thus
changing its behavior with every new invocation. This is
the opposite of referential transparency, and if the compiler
decided to convert `refNat1` to the form of `refNat2` as an
optimization, we would start to see different behavior probably
depending on the optimization level set at the compiler.

### But what about `IO`?

Yes, we need to talk about how `IO` works under the hood and
how it upholds referential transparency. Obviously, a
function such as `getLine` (of type `IO String`) yields
a different result every time it is run depending on
user input. How can *that* be referentially transparent.

Well, `IO a` is a wrapper around `PrimIO a`, and that is an alias
for `(1 w : %World) -> IORes a`. Now, what is *that* supposed to mean.
First, this value of type `%World` represents the current state
of the world: You computer's hard-drive, mouse position, the
temperature outside, number of babies currently filling their
diapers, everything: The whole universe. "How can that *fit*
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
invoke an `IO` action with the same arguments twice, so it
*does not have to* ever return the same result again.

Sounds like cheating? It is not. It actually works so well
and behaves exactly as expected, that huge effectful programs
can be safely built on top of this. But there is a caveat:
We are not supposed to have a value of type `%World`: It must
be provided by the runtime of our program when invoking the
`main` function. After that, the world state will be threaded
through the whole program, running all `IO` actions, which
will then return an "updated" world that will be passed on
downstream.

We can actually look at how this works with an example:

```idris
printTimePrim : PrimIO ()
printTimePrim w =
  let MkIORes t1 w2 := toPrim (clockTime UTC) w
      MkIORes () w3 := toPrim (putStrLn "The current time is: ") w2
      MkIORes () w4 := toPrim (printLn t1) w3
      MkIORes t2 w5 := toPrim (clockTime UTC) w4
      MkIORes () w6 := toPrim (putStrLn "Now the time is: ") w5
   in toPrim (printLn t1) w6
```

In the code above, we converted all `IO` actions to `PrimIO` functions
by using utility `toPrim`. This is allowed and a safe thing to do! In
`PrimIO`, we run computations with side effects by passing around
the `%World` token explicitly (starting with `w`). Every effectful
computation will consume the current world state, and - since it has
linear quantity - we will not be able to ever use it again. Instead,
we get a new value of type `%World` (again at quantity one) wrapped
up in an `IORes`: The "updated" world state. Therefore, it is perfectly
fine that the two calls to `clockTime UTC` (they read the current system
clock) do not return the same time: They are invoked with distinct
world tokens (`w` and `w4, respectively).

Of course, the code above is quite verbose, compared to other imperative
languages (because that's what it is: imperative code!), so we define
a monad on top of all of this `IO`, allowing us to run this stuff nicely
in a `do` block.

To sum this up: Every evaluation of an `IO` action consumes the
current world state, and we can't reuse it, nor will we ever get it back.
Therefore - by design - an `IO` action *can't* be invoked with the same
arguments twice, and so it does not have to ever return the same
result in a predictable manner.

<!-- vi: filetype=idris2:syntax=markdown
-->
