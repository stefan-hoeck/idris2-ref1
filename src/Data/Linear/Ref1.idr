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
data Ref : (s,a : Type) -> Type where
  R1 : (mut : Mut a) -> Ref s a

||| Alias for `Ref RIO`
public export
0 IORef : Type -> Type
IORef = Ref World

--------------------------------------------------------------------------------
-- utilities
--------------------------------------------------------------------------------

||| Creates a new mutable reference tagged with `tag` and holding
||| initial value `v`.
export %inline
ref1 : (v : a) -> F1 s (Ref s a)
ref1 v t = let m # t := ffi (prim__newIORef v) t in R1 m # t

|||
export %inline
newref : Lift1 s f => (v : a) -> f (Ref s a)
newref = lift1 . ref1

||| Creates a mutable reference in `IO` land.
|||
||| Deprecated: Use `newref` instead
export %inline %deprecate
newIORef : HasIO io => (v : a) -> io (IORef a)
newIORef v = runIO (ref1 v)

||| Reads the current value at a mutable reference tagged with `tag`.
export %inline
read1 : (r : Ref s a) -> F1 s a
read1 (R1 m) = ffi (prim__readIORef m)

||| Convenience alias for `runIO $ read1 r` for reading a reference in
||| `IO`.
export %inline
readref : Lift1 s f => Ref s a -> f a
readref = lift1 . read1

||| Updates the mutable reference tagged with `tag`.
export %inline
write1 : (r : Ref s a) -> (val : a) -> F1' s
write1 (R1 m) val = ffi (prim__writeIORef m val)

||| Convenience alias for `runIO $ write1 r v` for writing to a reference in
||| `IO`.
export %inline
writeref : Lift1 s f => Ref s a -> a -> f ()
writeref r = lift1 . write1 r

||| Atomically writes `val` to the mutable reference if its current
||| value is equal to `pre`.
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export %inline
caswrite1 : (r : Ref s a) -> (pre,val : a) -> F1 s Bool
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
casupdate1 : (r : Ref s a) -> (a -> (a,b)) -> F1 s b
casupdate1 r f t = assert_total (loop t)
  where
    covering loop : F1 s b
    loop t =
      let cur # t  := read1 r t
          (new,v)  := f cur
          True # t := caswrite1 r cur new t | _ # t => loop t
       in v # t

||| Atomically updates and reads a mutable reference in `IO`.
|||
||| This uses `casupdate1` internally.
export %inline
update : Lift1 s f => Ref s a -> (a -> (a,b)) -> f b
update r = lift1 . casupdate1 r

||| Atomic modification of a mutable reference using a CAS-loop
||| internally
|||
||| This is supported and has been tested on the Chez and Racket backends.
||| It trivially works on the JavaScript backends, which are single-threaded
||| anyway.
export
casmod1 : (r : Ref s a) -> (a -> a) -> F1' s
casmod1 r f t = assert_total (loop t)
  where
    covering loop : F1' s
    loop t =
      let cur  # t := read1 r t
          True # t := caswrite1 r cur (f cur) t | _ # t => loop t
       in () # t

||| Modifies the value stored in mutable reference tagged with `tag`.
export %inline
mod1 : (r : Ref s a) -> (f : a -> a) -> F1' s
mod1 r f t = let v # t2 := read1 r t in write1 r (f v) t2

||| Atomically modifies a mutable reference in `IO`.
|||
||| This uses `casmod1` internally.
export %inline
mod : Lift1 s f => Ref s a -> (a -> a) -> f ()
mod r = lift1 . casmod1 r

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the updated value.
export
modAndRead1 : (r : Ref s a) -> (f : a -> a) -> F1 s a
modAndRead1 r f t =
  let _ # t := mod1 r f t
   in read1 r t

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the previous value.
export
readAndMod1 : (r : Ref s a) -> (f : a -> a) -> F1 s a
readAndMod1 r f t =
  let v # t := read1 r t
      _ # t := write1 r (f v) t
   in v # t

||| Runs the given stateful computation only when given boolean flag
||| is currently at `True`
export
whenRef1 : (r : Ref s Bool) -> Lazy (F1' s) -> F1' s
whenRef1 r f t = let b # t1 := read1 r t in when1 b f t1

--------------------------------------------------------------------------------
-- Allocating mutable references
--------------------------------------------------------------------------------

||| Alias for a function taking a linear mutable refernce as
||| an auto-implicit argument.
public export
0 WithRef1 : (a,b : Type) -> Type
WithRef1 a b = forall s . (r : Ref s a) -> F1 s b

||| Runs a function requiring a linear mutable reference.
export
withRef1 : a -> WithRef1 a b -> b
withRef1 v f = run1 $ \t => let r # t := ref1 v t in f r t
