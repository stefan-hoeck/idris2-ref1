module Data.Linear.List

import public Data.Linear.Token

%default total

||| Filters a list using a predicate based on mutable
||| linear state.
export
filter1 : (a -> F1 s Bool) -> List a -> F1 s (List a)
filter1 f = go [<]
  where
    go : SnocList a -> List a -> F1 s (List a)
    go sx []        t = (sx <>> []) # t
    go sx (x :: xs) t =
      let b # t := f x t
       in if b then go (sx :< x) xs t else go sx xs t

||| Returns the first value in a list, for which the given
||| linear predicate returns `True`.
export
find1 : (a -> F1 s Bool) -> List a -> F1 s (Maybe a)
find1 f = go
  where
    go : List a -> F1 s (Maybe a)
    go []        t = Nothing # t
    go (x :: xs) t =
      let b # t := f x t
       in if b then Just x # t else go xs t

||| Returns the longest (possibly empty) prefix of the given list
||| for which the given predicate returns `True`.
|||
||| The second value of the pair returns the remainder of
||| the list.
export
span1 : (a -> F1 s Bool) -> List a -> F1 s (List a, List a)
span1 p = go [<]
  where
    go : SnocList a -> List a -> F1 s (List a, List a)
    go sx []        t = (sx<>>[], []) # t
    go sx (x :: xs) t =
      let b # t := p x t
       in if b then go (sx:<x) xs t else (sx<>>[],x::xs) # t

||| Like `span1` but returns the longest prefix, for which the
||| predicate does *not* hold.
export %inline
break1 : (a -> F1 s Bool) -> List a -> F1 s (List a, List a)
break1 p = span1 $ \v,t => let b # t := p v t in not b # t

||| Partitions the values in a list according to the given
||| linear predicate.
|||
||| Returns a pair of lists, the first of which holds the values
||| for which the predicate returned `False`. All other values
||| are returned in the second list.
export
partition1 : (a -> F1 s Bool) -> List a -> F1 s (List a, List a)
partition1 f = go [<] [<]
  where
    go : SnocList a -> SnocList a -> List a -> F1 s (List a, List a)
    go sx sy []        t = (sx <>> [], sy <>> []) # t
    go sx sy (x :: xs) t =
      let b # t := f x t
       in if b then go sx (sy:<x) xs t else go (sx:<x) sy xs t

||| Using a `Maybe` function to map and filter a list in one go.
export
mapMaybe1 : (a -> F1 s (Maybe b)) -> List a -> F1 s (List b)
mapMaybe1 f = go [<]
  where
    go : SnocList b -> List a -> F1 s (List b)
    go sx []        t = (sx <>> []) # t
    go sx (x :: xs) t =
      let Just v # t := f x t | Nothing # t => go sx xs t
       in go (sx :< v) xs t

||| Fills a list with values from a stateful linear computation.
export
replicate1 : Nat -> F1 s a -> F1 s (List a)
replicate1 n f = go [<] n
  where
    go : SnocList a -> Nat -> F1 s (List a)
    go sx 0     t = (sx <>> []) # t
    go sx (S k) t = let v # t2 := f t in go (sx :< v) k t2
