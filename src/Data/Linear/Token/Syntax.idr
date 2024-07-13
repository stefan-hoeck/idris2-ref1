module Data.Linear.Token.Syntax

import public Data.Linear.Token

%default total

export %inline
pure : a -> F1 s a
pure = (#)

export
(>>=) : F1 s a -> (a -> F1 s b) -> F1 s b
(>>=) f g t1 = let v # t2 := f t1 in g v t2

export
(>>) : F1' s -> F1 s b -> F1 s b
(>>) f g t = g (f t)

export
(<*>) : F1 s (a -> b) -> F1 s a -> F1 s b
(<*>) f g t =
  let fn # t2 := f t
      v  # t3 := g t2
   in fn v # t3
