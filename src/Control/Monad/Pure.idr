module Control.Monad.Pure

import public Data.Linear.Token

%default total

||| A monad of pure computations with suport for localized
||| mutable state.
|||
||| When universally quantified over `s`, this is like
||| `Control.Monad.ST` from base, but proper compiler support
||| for efficient code generation.
|||
||| On the other hand, `Pure World` is isomorphic to `IO`.
public export
record Pure (s,a : Type) where
  constructor P
  run : F1 s a

%inline
bind : Pure s a -> (a -> Pure s b) -> Pure s b

export %inline
Functor (Pure s) where
  map f (P g) = P $ mapF1 f g

export %inline
Applicative (Pure s) where
  pure v    = P (v #)
  ff <*> fv = bind ff (<$> fv)

export %inline
Monad (Pure s) where
  (>>=) = bind

export %inline
Lift1 s (Pure s) where
  lift1 = P

export %inline
HasIO (Pure World) where
  liftIO = lift1 . ioToF1

||| Runs a pure computation, probably with localized mutable state.
export %inline
runPure : (forall s . Pure s a) -> a
runPure p = run1 p.run

||| `Pure World` can be run in any monad that wraps `IO`.
export %inline
runPureIO : HasIO io => Pure World a -> io a
runPureIO = runIO . run
