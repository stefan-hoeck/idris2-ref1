||| A `Deferred s` value, is an observable, initially empty
||| reference that can be set exactly once. As such, it is an
||| important synchronization primitive.
|||
||| As with other mutable references, `Deferred` values can be safely used
||| in pure code as long as they are used locally in state thread.
module Data.Linear.Deferred

import public Data.Linear.Token
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.Linear.Unique
import Data.SortedMap

%default total

-- internal state of a `Deferred` value
data ST : Type -> Type -> Type where
  Val : (v : a) -> ST s a
  Obs : (cbs : SortedMap (Token s) (a -> F1' s)) -> ST s a

-- internal state of a `Once` value
data ST1 : Type -> Type -> Type where
  Ini1 : ST1 s a
  Val1 : (v : a) -> ST1 s a
  Obs1 : (cb : a -> F1' s) -> ST1 s a

--------------------------------------------------------------------------------
-- Once
--------------------------------------------------------------------------------

||| An atomic reference that can be set exactly once and observed
||| by at most one observer. All operations on `Once` are thread-safe.
|||
||| There are many occasions when it is enough to be able to register
||| only one observer. Use `Once` for these, and use `Deferred` in
||| case you need to register many observers.
export
record Once s a where
  constructor O
  ref : Ref s (ST1 s a)

||| Creates a new, empty `Once`.
export %inline
once1 : F1 s (Once s a)
once1 t = let ref # t := ref1 Ini1 t in O ref # t

||| Convenience alias of `once1`, which takes the type of
||| the value stored as an explicit argument.
export %inline
onceOf1 : (0 a : _) -> F1 s (Once s a)
onceOf1 _ = once1

unobs1 : Ref s (ST1 s a) -> F1' s
unobs1 ref =
  casmod1 ref $ \case
    Obs1 _ => Ini1
    v      => v

||| Returns `True` if a value has been set at the given `Once`.
export %inline
completedOnce1 : Once s a -> F1 s Bool
completedOnce1 (O r) t =
  let Val1 _ # t := read1 r t | _ # t => False # t
   in True # t

||| Reads the set value of a `Deferred1`. Returns `Nothing`,
||| if no value has been set yet.
export
peekOnce1 : Once s a -> F1 s (Maybe a)
peekOnce1 (O ref) t =
  let Val1 x # t := read1 ref t | _ # t => Nothing # t
   in Just x # t

||| Atomically tries to write the given value to a `Once`.
|||
||| The value is written if and only if no other value has
||| been set first. If an observer has been registered, it will be
||| invoked immediately.
export
putOnce1 : Once s a -> (v : a) -> F1' s
putOnce1 (O ref) v t =
  let act # t := casupdate1 ref upd t
   in act t

  where
    upd : ST1 s a -> (ST1 s a, F1' s)
    upd (Val1 x)  = (Val1 x, unit1)
    upd (Obs1 cb) = (Val1 v, cb v)
    upd Ini1      = (Val1 v, unit1)

||| Observe a `Once` by installing a callback.
|||
||| The callback is invoked immediately in case the value has
||| already been set.
|||
||| The action that is returned by this function can be used to
||| unregister the observer.
|||
||| Note: `Once` values can only be observed
|||       by one observer. Use `Deferred` in case you need to install
|||       many observers. In case another observer has already been set,
|||       this is a no-op and the callback never invoked.
export
observeOnce1 : Once s a -> (a -> F1' s) -> F1 s (F1' s)
observeOnce1 (O ref) cb t =
  let act # t := casupdate1 ref upd t
   in act t

  where
    upd : ST1 s a -> (ST1 s a, F1 s (F1' s))
    upd (Val1 x) = (Val1 x, \t => let _ # t := cb x t in unit1 # t)
    upd Ini1     = (Obs1 cb, (unobs1 ref #))
    upd x        = (x, (unit1 #))

--------------------------------------------------------------------------------
-- Deferred
--------------------------------------------------------------------------------

||| An atomic reference that can be set exactly once and observed
||| by an arbitrary number of observers. Any operations on a `Deferred`
||| are thread-safe.
export
record Deferred s a where
  constructor D
  ref : Ref s (ST s a)

||| Creates a new, empty `Deferred s a`.
export %inline
deferred1 : F1 s (Deferred s a)
deferred1 t = let ref # t := ref1 (Obs empty) t in D ref # t

||| Convenience alias of `deferred1`, which takes the type of
||| the value stored as an explicit argument.
export %inline
deferredOf1 : (0 a : _) -> F1 s (Deferred s a)
deferredOf1 _ = deferred1

||| Returns `True` if a value has been set at the given `Deferred`.
export %inline
completed1 : Deferred s a -> F1 s Bool
completed1 (D r) t =
  let Val _ # t := read1 r t | _ # t => False # t
   in True # t

||| Reads the set value of a `Deferred`. Returns `Nothing`,
||| if no value has been set yet.
export
peekDeferred1 : Deferred s a -> F1 s (Maybe a)
peekDeferred1 (D ref) t =
  let Val x # t := read1 ref t | _ # t => Nothing # t
   in Just x # t

||| Atomically tries to write the given value to a `Deferred`.
|||
||| The value is written if and only if no other values has
||| been set first. Any observers will be invoked immediately.
export
putDeferred1 : Deferred s a -> (v : a) -> F1' s
putDeferred1 (D ref) v t =
  let act # t := casupdate1 ref upd t
   in act t

  where
    upd : ST s a -> (ST s a, F1' s)
    upd (Val x)   = (Val x, unit1)
    upd (Obs cbs) = (Val v, traverse1_ (\cb => cb v) (Prelude.toList cbs))

unobs : Deferred s a -> Token s -> F1 s ()
unobs (D ref) tok =
  casmod1 ref $ \case
    Obs cbs => Obs $ delete tok cbs
    v       => v

||| Observe a `Deferred` by installing a callback using the given
||| token for identification.
|||
||| The callback is invoked immediately in case the value has
||| already been set.
|||
||| The action that is returned by this function can be used to
||| unregister the observer.
export
observeDeferredAs1 : Deferred s a -> Token s -> (a -> F1' s) -> F1 s (F1' s)
observeDeferredAs1 (D ref) tok cb t =
  let act # t := casupdate1 ref upd t
   in act t

  where
    upd : ST s a -> (ST s a, F1 s (F1' s))
    upd (Val x)   = (Val x, \t => let _ # t := cb x t in unit1 # t)
    upd (Obs cbs) = (Obs (insert tok cb cbs), (unobs (D ref) tok #))

||| Observe a `Deferred` by installing a callback.
|||
||| The callback is invoked immediately in case the value has
||| already been set.
|||
||| The action that is returned by this function can be used to
||| unregister the observer.
export %inline
observeDeferred1 : Deferred s a -> (a -> F1' s) -> F1 s (F1' s)
observeDeferred1 def cb t =
  let tok # t := token1 t
   in observeDeferredAs1 def tok cb t

--------------------------------------------------------------------------------
-- Lift1 Utilities
--------------------------------------------------------------------------------

||| Lifted version of `once1`
export %inline
once : Lift1 s f => f (Once s a)
once = lift1 once1

||| Lifted version of `onceOf`
export %inline
onceOf : Lift1 s f => (0 a : _) -> f (Once s a)
onceOf _ = once

||| Lifted version of `peekOnce1`
export %inline
peekOnce : Lift1 s f => Once s a -> f (Maybe a)
peekOnce o = lift1 $ peekOnce1 o

||| Lifted version of `completedOnce1`
export %inline
completedOnce : Lift1 s f => Once s a -> f Bool
completedOnce d = lift1 $ completedOnce1 d


||| Lifted version of `putOnce1`
export %inline
putOnce : Lift1 s f => Once s a -> (v : a) -> f ()
putOnce o v = lift1 $ putOnce1 o v

||| Lifted version of `completed1`
export %inline
completed : Lift1 s f => Deferred s a -> f Bool
completed d = lift1 $ completed1 d

||| Lifted version of `deferred1`
export %inline
deferred : Lift1 s f => f (Deferred s a)
deferred = lift1 deferred1

||| Lifted version of `deferredOf1`
export %inline
deferredOf : Lift1 s f => (0 a : _) -> f (Deferred s a)
deferredOf _ = deferred

||| Lifted version of `peekDeferred1`
export %inline
peekDeferred : Lift1 s f => Deferred s a -> f (Maybe a)
peekDeferred d = lift1 $ peekDeferred1 d

||| Lifted version of `putDeferred1`
export %inline
putDeferred : Lift1 s f => Deferred s a -> (v : a) -> f ()
putDeferred d v = lift1 $ putDeferred1 d v
