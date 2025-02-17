module Data.Linear.Token

import public Data.Linear

%default total

||| An empty type for tagging linear computations that can be wrapped in `IO`
public export
data World : Type where

--------------------------------------------------------------------------------
-- T1
--------------------------------------------------------------------------------

||| A linear token used in computations with mutable linear state.
|||
||| The idea is that mutable state (mutable references, arrays, pointers,
||| and so on) can only be accessed in the presence of the linear token
||| that was used to create the mutable resource.
|||
||| The advantage of using linear types over the `ST` monad: They come
||| without the (significant) performance overhead of monadic code in
||| Idris. Like the `ST` monad, this provides safe resource handling, because
||| the function for running linear computations over a `T1` (function
||| `run1`) must work with function argument `f` of type
||| `forall s . (1 t : T1 s) -> R1 s a`, that is, mutable references cannot
||| leak out of the linear computation and remain usable.
export %noinline %tcinline
0 T1 : (s : Type) -> Type
T1 s = %World

||| The result of a stateful linear computation.
|||
||| It pairs the result value with a new linear token.
public export
data R1 : (s,a : Type) ->  Type where
  (#) : (v : a) -> (1 tok : T1 s) -> R1 s a

||| `R1` is a functor, but since `map` does not have the correct
||| quantities, this is what we use instead.
export %inline
mapR1 : (a -> b) -> (1 r : R1 s a) -> R1 s b
mapR1 f (v # t) = f v # t

||| A linear computation operating on resources `rs` that produces a
||| result of type `a` with a new token operating on resources `ss`.
public export
0 F1 : (s : Type) -> (a : Type) -> Type
F1 s a = (1 t : T1 s) -> R1 s a

||| Convenience alias for `F1 s ()`.
public export
0 F1' : (s : Type) -> Type
F1' s = F1 s ()

||| `F1` is a functor, but since it is a function type, we cannot
||| implement an interface for it (but see `Control.Monad.Pure`).
export %inline
mapF1 : (a -> b) -> F1 s a -> F1 s b
mapF1 f act t = mapR1 f (act t)

||| Runs a linear computation by providing it with its own linear token.
|||
||| Since this is universally quantified over `s`, it is impossible that
||| callers can freely choose the tag for the state thread and thus reuse
||| their mutable references.
|||
||| It is also not possible that the linear token paired with the
||| corresponding mutable state leaks into the outer world, because
||| the result value must have quantity omega (see the definition of `R1`).
export %noinline
run1 : (forall s . F1 s a) -> a
run1 f = let v # _ := f {s = ()} %MkWorld in v

||| Runs a linear computation tagged with `[World]` as a primitive
||| `IO` action.
export %inline
primRun : F1 World a -> PrimIO a
primRun f w = let v # w := f w in MkIORes v w

||| Convenience wrapper around `primRun`.
export %inline
runIO : HasIO io => F1 World a -> io a
runIO f = primIO $ primRun f

||| Safely uses a primitive `IO` action in `F1 [World]`.
export %inline
toF1 : PrimIO a -> F1 World a
toF1 f w = let MkIORes v w := f w in v # w

||| Safely uses an `IO` action in `F1 [World]`.
export %inline
ioToF1 : IO a -> F1 World a
ioToF1 io = toF1 (toPrim io)

||| Run the given stateful computation if the boolean value is `True`.
export
when1 : Bool -> Lazy (F1' s) -> F1' s
when1 True  f t = f t
when1 False _ t = () # t

||| Run a stateful computation `n` times
export
forN : Nat -> F1' s -> F1' s
forN 0     f t = () # t
forN (S k) f t =
  let _ # t := f t
   in forN k f t

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

||| Use this to convert a primitive FFI call to a linear function
||| of type `F1 rs a`.
|||
||| This is typically used for running effectful computations that
||| do not produce an interesting result.
||| See `Data.Linear.Ref1.prim__writeRef` and
||| the corresponding `Data.Linear.Ref1.write1` for a usage example.
export %inline
ffi : PrimIO a -> F1 s a
ffi prim w = let MkIORes v w := prim w in v # w

--------------------------------------------------------------------------------
-- Lift1
--------------------------------------------------------------------------------

||| An interface for wrapping linear computations in a monadic context.
|||
||| This allows us to deal with pure as well as effectful computations.
||| Effectful computations should use `World` as the tag for `s`, while
||| pure computations should use universal quantification.
public export
interface Monad f => Lift1 (0 s : Type) (0 f : Type -> Type) | f where
  lift1 : F1 s a -> f a

export %inline
Lift1 World IO where
  lift1 = runIO

public export
0 IO1 : Type -> Type
IO1 = F1 World
