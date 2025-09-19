module Syntax.T1

import public Data.List.Quantifiers
import public Data.Linear.Token

%default total

export %inline
map1 : (a -> b) -> F1 s a -> F1 s b
map1 f g t = let v # t := g t in f v # t

export %inline
(<$>) : (a -> b) -> F1 s a -> F1 s b
(<$>) = map1

export %inline
(<&>) : F1 s a -> (a -> b) -> F1 s b
(<&>) = flip map1

export %inline
ignore1 : F1 s a -> F1' s
ignore1 f t = let _ # t := f t in () # t

export %inline
pure : a -> F1 s a
pure = (#)

export %inline
(>>=) : F1 s a -> (a -> F1 s b) -> F1 s b
(>>=) f g t1 = let v # t2 := f t1 in g v t2

export %inline
(>>) : F1' s -> F1 s b -> F1 s b
(>>) f g = T1.(>>=) f (\(),t => g t)

export %inline
(<*) : F1 s b -> F1' s -> F1 s b
(<*) f g t =
  let v # t := f t
      _ # t := g t
   in v # t

export %inline
(<*>) : F1 s (a -> b) -> F1 s a -> F1 s b
(<*>) f g = T1.do
  fn <- f
  v  <- g
  pure (fn v)
