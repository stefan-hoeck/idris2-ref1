module Data.Linear.Token

import public Data.Linear

%default total

||| `Ur` is an abbreviation for "unrestricted", meaning the wrapped value
||| can be used an arbitrary number of times, even if the `Ur` itself is used
||| in a linear context.
public export
0 Ur : Type -> Type
Ur = (!*)

||| A linear token used in computations with mutable linear state.
|||
||| The idea is to use the actual mutable references as auto-implicit
||| arguments that can also be easily listed in `parameters` blocks for
||| more complex computations. The `s` tag is used to make sure a
||| mutable reference cannot be accessed without the corresponding
||| linear token. This is the same technique used to make sure mutable
||| reference do not leak out of the `ST` monad in `Control.Monad.ST` in
||| base.
|||
||| The advantage of using linear types over the `ST` monad: They come
||| without the (significant) performance overhead of monadic code in
||| Idris.
export
data T1 : (s : Type) -> Type where [external]

%name T1 t,t1,t2,t3

%inline token : T1 s
token = believe_me (the Bits8 0)

drop : a -> T1 s -> a
drop v _ = v

||| Drop a linear token. All associated mutable references and arrays
||| will no longer be accessible.
export %inline
discard : (1 t : T1 s) -> (v : a) -> a
discard t x = assert_linear (drop x) t

||| The result of a stateful linear computation.
|||
||| It pairs the result value with a new linear token.
public export
data R1 : (s : Type) -> (a : Type) ->  Type where
  (#) : (v : a) -> (1 tok : T1 s) -> R1 s a

||| `R1` is a functor, but since `map` does not have the correct
||| quantities, this is what we use instead.
export
mapR1 : (a -> b) -> (1 r : R1 s a) -> R1 s b
mapR1 f (v # t) = f v # t

||| A linear computation in state thread `s` that only updates
||| the state without producing an interesting result.
public export
0 F1' : (s : Type) -> Type
F1' s = T1 s -@ T1 s

||| A linear computation in state thread `s` that produces a
||| result of type `a`.
public export
0 F1 : (s : Type) -> (a : Type) -> Type
F1 s a = T1 s -@ R1 s a

||| Runs a linear computation by providing it with its own linear token.
|||
||| Since this is universally quantified over `s`, it is impossible that
||| callers can freely choose the tag for the state thread and thus reuse
||| their mutable references.
|||
||| It is also not possible that the linear token paired with the
||| corresponding mutable state leaks into the outer world, because
||| the result value must have quantity omega (see the definition of `R1`).
export %inline
run1 : (forall s . F1 s a) -> a
run1 f = let v # t1 := f {s = ()} token in discard t1 v

||| Sometimes, it is necessary to let callers decide, when they want to
||| get rid of the linear token. This is, for instance, necessary when
||| converting a mutable array to an immutable one.
|||
||| In order to do this safely, the mutable array needs to be copied, because
||| it might still be updated later on. However, in many occasions this is
||| inefficient, because the whole point of using a mutable array is to
||| eventually convert it to an immutable one. Then the conversion
||| can happen without copying, if and only if
||| the linear token is destroyed at the same time which renders the mutable
||| array (tagged to the now destroyed token) useless.
export %inline
runUr : (forall s . (1 t : T1 s) -> Ur a) -> a
runUr f = unrestricted (f {s = ()} token)

||| Run the given stateful computation if the boolean value is `True`.
export
when1 : Bool -> Lazy (F1' s) -> F1' s
when1 True  f t = f t
when1 False _ t = t

||| Run a stateful computation `n` times
export
forN : Nat -> F1' s -> F1' s
forN 0     f t = t
forN (S k) f t = forN k f (f t)
