module Data.Linear.Token

import public Data.Linear

%default total

--------------------------------------------------------------------------------
-- Resources
--------------------------------------------------------------------------------

||| A tag for marking resources that can be used both in `IO` or in pure
||| computations.
public export
data RTag = RPure | RIO

||| A tag for linear computation that should be run in `IO`
public export
data World : Type where

||| Interface for tagging types that should be evaluated in
||| `IO` land.
public export
interface InIO a where

||| A list of arbitrary managed resources.
|||
||| This is used as parameter for the linear token `T1`
||| provided by this library. The idea is that only resources
||| bound to the linear token can be used in the current linear
||| context.
|||
||| We distinguish between two cases: Values that belong to `IO` land
||| (i.e. mutable references and arrays coming from and being sent
||| to the FFI), and values that should be created (and, possibly, release)
||| in pure computations.
|||
||| For the former types of values, `Resources` should be equal to `[World]`,
||| and the corresponding types should implement interface `InIO`. These
||| values can be freely used in linear computations involving a linear
||| token of type `T1 [World] a`, but running these computations is an `IO`
||| action.
|||
||| For the latter type of values (those being used in pure computations),
||| `T1 rs a` should be used, where `rs` is a list of linear resources bound
||| to the linear token.
public export
data Resources : Type where
  Nil  : Resources
  (::) : {0 t : Type} -> (v : t) -> Resources -> Resources

||| Proof that resource `r` is in the list of resources `rs`.
public export
data Res : (r : t) -> (rs : Resources) -> Type where
  RH : Res r (r::rs)
  RT : Res r rs -> Res r (s::rs)
  RW : {0 t : Type} -> {0 r : t} -> InIO t => Res r [World]

||| Removes resource `r` from the list of managed resources `rs`.
public export
0 Drop : (rs : Resources) -> Res r rs -> Resources
Drop (r :: rs) RH     = rs
Drop (s :: rs) (RT x) = s :: Drop rs x
Drop [World]   RW     = [World]

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
||| Idris. In addition, this provides safe resource handling, because
||| the function for running linear computations over a `T1` (function
||| `run1` must work with function argument `f` of type
||| `(1 t : T1 []) -> R1 [] a`, that is, any resources required must
||| be allocated and released within `f`.
export %noinline %tcinline
0 T1 : (rs : Resources) -> Type
T1 rs = %World

||| The result of a stateful linear computation.
|||
||| It pairs the result value with a new linear token.
public export
data Res1 : (a : Type) -> (f : a -> Resources) ->  Type where
  (#) : (v : a) -> (1 tok : T1 (f v)) -> Res1 a f

public export
0 R1 : Resources -> Type -> Type
R1 rs a = Res1 a (const rs)

public export
0 A1 : Resources -> Type -> Type
A1 rs a = Res1 a (::rs)

||| `R1` is a functor, but since `map` does not have the correct
||| quantities, this is what we use instead.
export
mapR1 : (a -> b) -> (1 r : R1 rs a) -> R1 rs b
mapR1 f (v # t) = f v # t

||| A computation mutating some state where resources a allocated or
||| released.
public export
0 C1' : (rs,ss : Resources) -> Type
C1' rs ss = T1 rs -@ R1 ss ()

||| Convenience alias for `C1' rs rs`.
public export
0 F1' : (rs : Resources) -> Type
F1' rs = C1' rs rs

||| A linear computation operating on resources `rs` that produces a
||| result of type `a` with a new token operating on resources `ss`.
public export
0 C1 : (rs,ss : Resources) -> (a : Type) -> Type
C1 rs ss a = T1 rs -@ R1 ss a

||| Convenience alias for `C1 rs rs`
public export
0 F1 : (rs : Resources) -> (a : Type) -> Type
F1 rs = C1 rs rs

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
run1 : F1 [] a -> a
run1 f = let v # _ := f %MkWorld in v

||| Runs a linear computation tagged with `[World]` as a primitive
||| `IO` action.
export %inline
primRun : F1 [World] a -> PrimIO a
primRun f w = let v # w := f w in MkIORes v w

||| Convenience wrapper around `primRun`.
export %inline
runIO : HasIO io => F1 [World] a -> io a
runIO f = primIO $ primRun f

||| Safely uses a primitive `IO` action in `F1 [World]`.
export %inline
toF1 : PrimIO a -> F1 [World] a
toF1 f w = let MkIORes v w := f w in v # w

||| Safely uses an `IO` action in `F1 [World]`.
export %inline
ioToF1 : IO a -> F1 [World] a
ioToF1 io = toF1 (toPrim io)

||| Run the given stateful computation if the boolean value is `True`.
export
when1 : Bool -> Lazy (F1' rs) -> F1' rs
when1 True  f t = f t
when1 False _ t = () # t

||| Run a stateful computation `n` times
export
forN : Nat -> F1' rs -> F1' rs
forN 0     f t = () # t
forN (S k) f t =
  let _ # t := f t
   in forN k f t

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

||| Bind a new resource to the current linear token.
|||
||| This is for library authors when writing FFI bindings.
||| Do not use it unless you know what you are doing! Never use this to
||| bind an existing resource to a different linear token as this will
||| make it possible to reuse a mutable reference in a different
||| linear context, thus breaking referential transparency.
|||
||| Library authors should use this for allocating new resources
||| that can then be accessed via the updated linear token.
||| See `Data.Linear.Ref1.prim__newRef` and the corresponding
||| `Data.Linear.Ref1.ref1` for a usage example.
export %inline
unsafeBind : (1 t : T1 rs) -> T1 (r::rs)
unsafeBind w = w

||| Release a resource from the token it was bound to.
|||
||| This is for library authors when writing FFI bindings.
||| Do not use it unless you know what you are doing! Never use this to
||| release a resource without actually doing the releasing too (such as
||| freeing the memory allocated for a pointer)!
|||
||| Library authors should use this to remove a resource from the
||| list of resources managed by a linear token. This should happen
||| at the same time when the resource is actually released by an
||| FFI call if necessary.
||| See `Data.Linear.Ref1.release` for a basic usage example that does
||| not actually release anything since our mutable references are garbage
||| collected.
|||
||| A better usage example can be found in the idris2-array library,
||| where function `freeze` removes an array from the list of
||| managed resources and wraps it in an immutable array at the same
||| time. Since the mutable array can no longer be accessed with the
||| new linear token, it is safe to do this without copying the
||| mutable array!
export %inline
unsafeRelease : (0 p : Res r rs) -> C1' rs (Drop rs p)
unsafeRelease _ w = () # w

||| Use this to convert a primitive FFI call to a linear function
||| of type `F1 rs a`.
|||
||| This is typically used for running effectful computations that
||| do not produce an interesting result.
||| See `Data.Linear.Ref1.prim__writeRef` and
||| the corresponding `Data.Linear.Ref1.write1` for a usage example.
export %inline
ffi : PrimIO a -> F1 rs a
ffi prim w = let MkIORes v w := prim w in v # w
