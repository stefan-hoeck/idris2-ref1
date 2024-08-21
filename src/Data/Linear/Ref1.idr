module Data.Linear.Ref1

import public Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- Prim Calls
--------------------------------------------------------------------------------

-- Implemented externally
-- e.g., in Scheme, passed around as a box
data Mut : Type where [external]

export %foreign "scheme:(lambda (x) (box x))"
                "javascript:lambda:(x) => ({value : x})"
prim__newRef   : AnyPtr -> Mut

export %foreign "scheme:(lambda (x) (unbox x))"
                "javascript:lambda:(x) => x.value"
prim__readRef  : Mut -> AnyPtr

export %foreign "scheme:(lambda (x v) (set-box! x v))"
                "javascript:lambda:(x,v,t) => {x.value = v}"
prim__writeRef : Mut -> (val : AnyPtr) -> PrimIO ()

--------------------------------------------------------------------------------
-- Ref1: A linearily mutable reference
--------------------------------------------------------------------------------

||| A linear mutable reference
export
data Ref1 : (a : Type) -> Type where
  R1 : (mut : Mut) -> Ref1 a

--------------------------------------------------------------------------------
-- utilities
--------------------------------------------------------------------------------

||| Creates a new mutable reference tagged with `tag` and holding
||| initial value `v`.
export %inline
ref1 : (v : a) -> (1 t : T1 rs) -> A1 rs (Ref1 a)
ref1 v t = A (R1 $ prim__newRef $ believe_me v) (unsafeBind t)

||| Reads the current value at a mutable reference tagged with `tag`.
export %inline
read1 : (r : Ref1 a) -> (0 p : Res r rs) => F1 rs a
read1 (R1 m) t = believe_me (prim__readRef m) # t

||| Updates the mutable reference tagged with `tag`.
export %inline
write1 : (r : Ref1 a) -> (0 p : Res r rs) => (val : a) -> F1' rs
write1 (R1 m) val = ffi (prim__writeRef m (believe_me val))

||| Modifies the value stored in mutable reference tagged with `tag`.
export %inline
mod1 : (r : Ref1 a) -> (0 p : Res r rs) => (f : a -> a) -> F1' rs
mod1 r f t = let v # t2 := read1 r t in write1 r (f v) t2

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the updated value.
export
modAndRead1 : (r : Ref1 a) -> (0 p : Res r rs) => (f : a -> a) -> F1 rs a
modAndRead1 r f t =
  let _ # t := mod1 r f t
   in read1 r t

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the previous value.
export
readAndMod1 : (r : Ref1 a) -> (0 p : Res r rs) => (f : a -> a) -> F1 rs a
readAndMod1 r f t =
  let v # t := read1 r t
      _ # t := write1 r (f v) t
   in v # t

||| Runs the given stateful computation only when given boolean flag
||| is currently at `True`
export
whenRef1 : (r : Ref1 Bool) -> (0 p : Res r rs) => Lazy (F1' rs) -> F1' rs
whenRef1 r f t = let b # t1 := read1 r t in when1 b f t1

||| Releases a mutable reference.
|||
||| It will no longer be accessible through the given linear token.
export %noinline
release : (r : Ref1 a) -> (0 p : Res r rs) => C1' rs (Drop rs p)
release r t = unsafeRelease p t

||| Read and releases a mutable reference.
|||
||| It will no longer be accessible through the given linear token.
export %inline
readAndRelease :
     (r : Ref1 a)
  -> {auto 0 p : Res r rs}
  -> C1 rs (Drop rs p) a
readAndRelease r t =
  let v # t := read1 r t
      _ # t := release r t
   in v # t

--------------------------------------------------------------------------------
-- Allocating mutable references
--------------------------------------------------------------------------------

||| Alias for a function taking a linear mutable refernce as
||| an auto-implicit argument.
public export
0 WithRef1 : (a,b : Type) -> Type
WithRef1 a b = (r : Ref1 a) -> F1 [r] b

||| Runs a function requiring a linear mutable reference.
export
withRef1 : a -> WithRef1 a b -> b
withRef1 v f =
  run1 $ \t =>
    let A r t := ref1 v t
        v # t := f r t
        _ # t := release r t
     in v # t
