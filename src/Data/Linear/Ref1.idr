module Data.Linear.Ref1

import public Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- Prim Calls
--------------------------------------------------------------------------------

-- Implemented externally
-- e.g., in Scheme, passed around as a box
data Mut : Type -> Type where [external]

%extern prim__newIORef : forall a . a -> (1 x : %World) -> IORes (Mut a)
%extern prim__readIORef : forall a . Mut a -> (1 x : %World) -> IORes a
%extern prim__writeIORef : forall a . Mut a -> (1 val : a) -> (1 x : %World) -> IORes ()


%foreign "scheme:(lambda (a x v w) (if (box-cas! x v w) 1 0))"
         "javascript:lambda:(a,x,v,w) => {if (x.value === v) {x.value = w; return 1;} else {return 0;}}"
prim__casWrite : Mut a -> (prev,val : a) -> Bits8

--------------------------------------------------------------------------------
-- Ref1: A linearily mutable reference
--------------------------------------------------------------------------------

||| A linear mutable reference
export
data Ref : RTag -> (a : Type) -> Type where
  R1 : (mut : Mut a) -> Ref t a

||| Alias for `Ref RPure`
public export
0 Ref1 : Type -> Type
Ref1 = Ref RPure

||| Alias for `Ref RIO`
public export
0 IORef : Type -> Type
IORef = Ref RIO

public export
InIO (Ref RIO a) where

--------------------------------------------------------------------------------
-- utilities
--------------------------------------------------------------------------------

||| Creates a new mutable reference tagged with `tag` and holding
||| initial value `v`.
export %inline
ref1 : (v : a) -> (1 t : T1 rs) -> A1 rs (Ref1 a)
ref1 v t = let m # t := ffi (prim__newIORef v) t in R1 m # unsafeBind t

||| Creates a mutable reference in `IO` land.
export %inline
refIO : (v : a) -> F1 [World] (IORef a)
refIO v t = let m # t := ffi (prim__newIORef v) t in R1 m # t

||| Creates a mutable reference in `IO` land.
export %inline
newIORef : HasIO io => (v : a) -> io (IORef a)
newIORef v =
  primIO $ \w => let MkIORes m w := prim__newIORef v w in MkIORes (R1 m) w

||| Reads the current value at a mutable reference tagged with `tag`.
export %inline
read1 : (r : Ref t a) -> (0 p : Res r rs) => F1 rs a
read1 (R1 m) = ffi (prim__readIORef m)

||| Convenience alias for `runIO $ read1 r` for reading a reference in
||| `IO`.
export %inline
readref : HasIO io => IORef a -> io a
readref r = runIO $ read1 r

||| Updates the mutable reference tagged with `tag`.
export %inline
write1 : (r : Ref t a) -> (0 p : Res r rs) => (val : a) -> F1' rs
write1 (R1 m) val = ffi (prim__writeIORef m val)

||| Convenience alias for `runIO $ write1 r v` for writing to a reference in
||| `IO`.
export %inline
writeref : HasIO io => IORef a -> a -> io ()
writeref r v = runIO $ write1 r v

||| Atomically writes `val` to the mutable reference if its current
||| value is equal to `pre`.
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export %inline
caswrite1 : (r : Ref t a) -> (0 p : Res r rs) => (pre,val : a) -> F1 rs Bool
caswrite1 (R1 m) pre val t =
  case prim__casWrite m pre val of
    0 => False # t
    _ => True # t

||| Atomic modification of a mutable reference using a CAS-loop
||| internally
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export
casupdate1 : (r : Ref t a) -> (a -> (a,b)) -> (0 p : Res r rs) => F1 rs b
casupdate1 r f t = assert_total (loop t)
  where
    covering loop : F1 rs b
    loop t =
      let cur # t  := read1 r t
          (new,v)  := f cur
          True # t := caswrite1 r cur new t | _ # t => loop t
       in v # t

||| Atomically updates and reads a mutable reference in `IO`.
|||
||| This uses `casupdate1` internally.
export %inline
update : HasIO io => IORef a -> (a -> (a,b)) -> io b
update r v = runIO $ casupdate1 r v

||| Atomic modification of a mutable reference using a CAS-loop
||| internally
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export
casmod1 : (r : Ref t a) -> (a -> a) -> (0 p : Res r rs) => F1' rs
casmod1 r f t = assert_total (loop t)
  where
    covering loop : F1' rs
    loop t =
      let cur  # t := read1 r t
          True # t := caswrite1 r cur (f cur) t | _ # t => loop t
       in () # t

||| Modifies the value stored in mutable reference tagged with `tag`.
export %inline
mod1 : (r : Ref t a) -> (0 p : Res r rs) => (f : a -> a) -> F1' rs
mod1 r f t = let v # t2 := read1 r t in write1 r (f v) t2

||| Atomically modifies a mutable reference in `IO`.
|||
||| This uses `casmod1` internally.
export %inline
mod : HasIO io => IORef a -> (a -> a) -> io ()
mod r f = runIO $ casmod1 r f

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the updated value.
export
modAndRead1 : (r : Ref t a) -> (0 p : Res r rs) => (f : a -> a) -> F1 rs a
modAndRead1 r f t =
  let _ # t := mod1 r f t
   in read1 r t

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the previous value.
export
readAndMod1 : (r : Ref t a) -> (0 p : Res r rs) => (f : a -> a) -> F1 rs a
readAndMod1 r f t =
  let v # t := read1 r t
      _ # t := write1 r (f v) t
   in v # t

||| Runs the given stateful computation only when given boolean flag
||| is currently at `True`
export
whenRef1 : (r : Ref t Bool) -> (0 p : Res r rs) => Lazy (F1' rs) -> F1' rs
whenRef1 r f t = let b # t1 := read1 r t in when1 b f t1

||| Releases a mutable reference.
|||
||| It will no longer be accessible through the given linear token.
export %inline
release : (r : Ref1 a) -> (0 p : Res r rs) => C1' rs (Drop rs p)
release r t = unsafeRelease p t

||| Read and releases a mutable reference.
|||
||| It will no longer be accessible through the given linear token.
export %inline
readAndRelease : (r : Ref1 a) -> (0 p : Res r rs) => C1 rs (Drop rs p) a
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
    let r # t := ref1 v t
        v # t := f r t
        _ # t := release r t
     in v # t
