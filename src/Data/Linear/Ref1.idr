module Data.Linear.Ref1

import public Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- Prim Calls
--------------------------------------------------------------------------------

-- Implemented externally
-- e.g., in Scheme, passed around as a box
data Mut : Type -> Type where [external]

%extern prim__newIORef   : a -> (1 x : %World) -> Mut a
%extern prim__readIORef  : Mut a -> (1 x : %World) -> a
%extern prim__writeIORef : Mut a -> (val : a) -> (1 x : %World) -> IORes ()

--------------------------------------------------------------------------------
-- Ref1: A linearily mutable reference
--------------------------------------------------------------------------------

||| A linear mutable reference tagged with resolution tag `tag`,
||| bound to linear state thread `s`, and holding values of type `a`.
|||
||| About the type parameters:
|||
|||   `tag`: The idea is to use `Ref1 tag s a` as an auto-implicit function
|||          argument, so that it can be conveniently used in `parameters`
|||          blocks. Since we might require more than one mutable reference,
|||          we need to be able to distinguish between them. This is what `tag` is
|||          for: The genral functions for creating, reading, and writing
|||          mutable references all take an erased `tag` argument to specify the
|||          reference we want to use (see `ref1At`, `read1At`, `write1At`,
|||          and other utility functions ending on "At").
|||
|||          If you only need one mutable reference in your function, consider
|||          using the utilities not ending on "At", which are specialized
|||          for working with references tagged with unit (`()`).
|||
|||   `s`:   Tag of the state thread the mutable reference is used in.
|||          In order to make sure a linear reference does not leak into
|||          the outer world, it is tagged with the state thread of the
|||          linear token it was created with. Thus, a mutable reference is
|||          invariably bound to its corresponding token. A mutable reference
|||          without its linear token is therefore utterly useless,
|||          because we are never free in choosing the value of `s`: It *must* be
|||          universally quantified, otherwise the linear computation cannot be
|||          run (see `Linear.Token.run1`).
|||
|||   `a`    Just the type of values this reference holds.
export
data Ref1 : (tag : k) -> (s,a : Type) -> Type where
  [search tag s]
  R1 : (mut : Mut a) -> Ref1 tag s a

--------------------------------------------------------------------------------
-- Tagged utilities
--------------------------------------------------------------------------------

||| Creates a new mutable reference tagged with `tag` and holding
||| initial value `v`.
export %inline
ref1At : (0 tag : _) -> (v : a) -> F1 s (Ref1 tag s a)
ref1At tag v t = R1 (prim__newIORef v %MkWorld) # t

||| Reads the current value at a mutable reference tagged with `tag`.
export %inline
read1At : (0 tag : _) -> Ref1 tag s a => F1 s a
read1At _ @{R1 m} t = prim__readIORef m %MkWorld # t

||| Updates the mutable reference tagged with `tag`.
export
write1At : (0 tag : _) -> Ref1 tag s a => (val : a) -> F1' s
write1At _ @{R1 m} val t =
  let MkIORes _ w := prim__writeIORef m val %MkWorld
   in t

||| Modifies the value stored in mutable reference tagged with `tag`.
export
mod1At : (0 tag : _) -> Ref1 tag s a => (f : a -> a) -> F1' s
mod1At tag f t =
  let v # t2 := read1At tag t
   in write1At tag (f v) t2

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the updated value.
export
modAndRead1At : (0 tag : _) -> Ref1 tag s a => (f : a -> a) -> F1 s a
modAndRead1At tag f t = read1At tag (mod1At tag f t)

||| Modifies the value stored in mutable reference tagged with `tag`
||| and returns the previous value.
export
readAndMod1At : (0 tag : _) -> Ref1 tag s a => (f : a -> a) -> F1 s a
readAndMod1At tag f t =
  let v # t2 := read1At tag t
   in v # write1At tag (f v) t2

--------------------------------------------------------------------------------
-- Default utilities
--------------------------------------------------------------------------------

||| `ref1At` specialized to `()`.
export %inline
ref1 : (v : a) -> F1 s (Ref1 () s a)
ref1 = ref1At ()

||| `read1At` specialized to `()`.
export %inline
read1 : Ref1 () s a => F1 s a
read1 = read1At ()

||| `write1At` specialized to `()`.
export %inline
write1 : Ref1 () s a => a -> F1' s
write1 = write1At ()

||| `mod1At` specialized to `()`.
export %inline
mod1 : Ref1 () s a => (f : a -> a) -> F1' s
mod1 = mod1At ()

||| `modAndRead1At` specialized to `()`.
export
modAndRead1 : Ref1 () s a => (f : a -> a) -> F1 s a
modAndRead1 = modAndRead1At ()

||| `readAndMod1At` specialized to `()`.
export
readAndMod1 : Ref1 () s a => (f : a -> a) -> F1 s a
readAndMod1 = readAndMod1At ()

--------------------------------------------------------------------------------
-- Allocating mutable references
--------------------------------------------------------------------------------

||| Alias for a function taking a linear mutable refernce as
||| an auto-implicit argument.
public export
0 WithRef1 : (a,b : Type) -> Type
WithRef1 a b = forall s . Ref1 () s a => F1 s b

||| Runs a function requiring a linear mutable reference.
export
withRef1 : a -> WithRef1 a b -> b
withRef1 v f =
  run1 $ \t => let ref # t2 := ref1 v t in f @{ref} t2
