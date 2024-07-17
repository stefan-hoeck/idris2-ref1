module Data.Linear.Token

import public Data.Linear

%default total

public export
data Resources : Type where
  Nil  : Resources
  (::) : {0 t : Type} -> (v : t) -> Resources -> Resources

public export
data Res : (r : t) -> Resources -> Type where
  RH : Res r (r::rs)
  RT : Res r rs -> Res r (s::rs)

public export
0 Drop : (rs : Resources) -> Res r rs -> Resources
Drop (r :: rs) RH     = rs
Drop (s :: rs) (RT x) = s :: Drop rs x

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
data T1 : (rs : Resources) -> Type where
  T : AnyPtr -> T1 rs

%name T1 t,t1,t2,t3

||| Bind a new resource to the current linear tag.
|||
||| This is for library authors when writing FFI bindings.
||| Do not use it unless you know what you are doing! Never use this to
||| bind an existing resource to a different linear token!
export %inline
unsafeBind : (1 t : T1 rs) -> T1 (r::rs)
unsafeBind (T p) = T p

||| Release a resource from the token it was bound to.
|||
||| This is for library authors when writing FFI bindings.
||| Do not use it unless you know what you are doing! Never use this to
||| release a resource without actually doing the releasing too (such as
||| freeing the memory allocated for it)!
export %inline
unsafeRelease : (0 p : Res r rs) -> (1 t : T1 rs) -> T1 (Drop rs p)
unsafeRelease _ (T t) = T t

||| The result of a stateful linear computation.
|||
||| It pairs the result value with a new linear token.
public export
data R1 : (rs : Resources) -> (a : Type) ->  Type where
  (#) : (v : a) -> (1 tok : T1 rs) -> R1 rs a

||| The result of allocating a linear resource
public export
data A1 : (rs : Resources) -> (a : Type) ->  Type where
  A : (v : a) -> (1 tok : T1 (v::rs)) -> A1 rs a

||| `R1` is a functor, but since `map` does not have the correct
||| quantities, this is what we use instead.
export
mapR1 : (a -> b) -> (1 r : R1 rs a) -> R1 rs b
mapR1 f (v # t) = f v # t

||| A computation mutating some state where resources a allocated or
||| released.
public export
0 C1' : (rs,ss : Resources) -> Type
C1' rs ss = T1 rs -@ T1 ss

||| Convenience alias for `C1' rs rs`.
public export
0 F1' : (rs : Resources) -> Type
F1' rs = C1' rs rs

||| A linear computation operating on resources `rs` that produces a
||| result of type `a`.
public export
0 F1 : (rs : Resources) -> (a : Type) -> Type
F1 rs a = T1 rs -@ R1 rs a

export %inline
ffi : ((1 p : AnyPtr) -> AnyPtr) -> F1' rs
ffi f (T t) = T (f t)

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
run1 f = let v # T _ := f (believe_me $ the Bits8 0) in v

||| Run the given stateful computation if the boolean value is `True`.
export
when1 : Bool -> Lazy (F1' rs) -> F1' rs
when1 True  f t = f t
when1 False _ t = t

||| Run a stateful computation `n` times
export
forN : Nat -> F1' rs -> F1' rs
forN 0     f t = t
forN (S k) f t = forN k f (f t)
