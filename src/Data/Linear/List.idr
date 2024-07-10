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
      let b # t1 := f x t
       in if b then go (sx :< x) xs t1 else go sx xs t1

||| Using a `Maybe` function to map and filter a list in one go.
export
mapMaybe1 : (a -> F1 s (Maybe b)) -> List a -> F1 s (List b)
mapMaybe1 f = go [<]
  where
    go : SnocList b -> List a -> F1 s (List b)
    go sx []        t = (sx <>> []) # t
    go sx (x :: xs) t =
      let Just v # t1 := f x t | Nothing # t1 => go sx xs t1
       in go (sx :< v) xs t1

||| Fills a list with values from a stateful linear computation.
export
replicate1 : Nat -> F1 s a -> F1 s (List a)
replicate1 n f = go [<] n
  where
    go : SnocList a -> Nat -> F1 s (List a)
    go sx 0     t = (sx <>> []) # t
    go sx (S k) t = let v # t2 := f t in go (sx :< v) k t2

