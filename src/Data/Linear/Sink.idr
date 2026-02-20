module Data.Linear.Sink

import Data.Contravariant
import Data.Linear.Deferred
import Data.Linear.Ref1
import Syntax.T1
import public Data.Linear.Token

%default total

||| A `Sink` is a primitive consumer of values.
public export
record Sink o where
  [noHints]
  constructor S
  sink1 : o -> IO1 ()

||| A `Sink` is a contravariant functor.
export %inline
cmap : (b -> a) -> Sink a -> Sink b
cmap f (S g) = S $ g . f

export %inline
Contravariant Sink where
  contramap = cmap

||| Create a `Sink` that collects values in a mutable
||| reference holding a `SnocList`.
|||
||| The current content of the sink can be read and cleared
||| by invoking the given linear action.
|||
||| The returned sink is thread-safe: Values from multiple
||| threads can be written to it.
export
snocSink1 : (0 a : Type) -> IO1 (Sink a, IO1 (List a))
snocSink1 a = T1.do
  ref <- ref1 [<]
  pure (S $ \v => casmod1 ref (:< v), readList ref)
  where
    readList : IORef (SnocList a) -> IO1 (List a)
    readList ref = casupdate1 ref $ \sv => ([<], sv <>> [])

export
Semigroup (Sink a) where
  S s1 <+> S s2 = S $ \v,t => let _ # t := s1 v t in s2 v t

export
Monoid (Sink a) where
  neutral = S $ \_,t => () # t

export %inline
sink : HasIO io => (s : Sink a) => a -> io ()
sink = runIO . s.sink1

export %inline
sinkAs : HasIO io => (0 a : Type) -> (s : Sink a) => a -> io ()
sinkAs a = sink

export %inline
sinkTo : HasIO io => (s : Sink a) -> a -> io ()
sinkTo s = runIO . s.sink1

export %inline
onceSink : Once World t -> Sink t
onceSink o = S (putOnce1 o)

export %inline
deferredSink : Deferred World t -> Sink t
deferredSink o = S (putDeferred1 o)
