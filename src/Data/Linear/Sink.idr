module Data.Linear.Sink

import Data.Contravariant
import Data.Linear.Ref1
import Syntax.T1
import public Data.Linear.Token

%default total

||| A `Sink` is a primitive consumer of values.
public export
record Sink o where
  [noHints]
  constructor S
  sink : o -> IO1 ()

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

