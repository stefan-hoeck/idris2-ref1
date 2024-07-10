module Data.Linear.Traverse1

import Data.List1
import Data.SnocList
import Data.Vect
import public Data.Linear.Token

%default total

--------------------------------------------------------------------------------
-- Foldable1
--------------------------------------------------------------------------------

||| Folds over a computation including potentially linear
||| mutable state.
public export
interface Foldable1 (0 f : Type -> Type) where
  foldl1     : (a -> e -> F1 s a) -> a -> f e -> F1 s a
  foldr1     : (e -> a -> F1 s a) -> a -> f e -> F1 s a
  foldMap1   : Monoid m => (a -> F1 s m) -> f a -> F1 s m
  traverse1_ : (a -> F1' s) -> f a -> F1' s

export
Foldable1 Maybe where
  foldl1 f v Nothing  t = v # t
  foldl1 f v (Just x) t = f v x t

  foldr1 f v Nothing  t = v # t
  foldr1 f v (Just x) t = f x v t

  foldMap1 f Nothing  t = neutral # t
  foldMap1 f (Just x) t = f x t

  traverse1_ f Nothing  t = t
  traverse1_ f (Just v) t = f v t

export
Foldable1 (Either e) where
  foldl1 f v (Left _)  t = v # t
  foldl1 f v (Right x) t = f v x t

  foldr1 f v (Left _)  t = v # t
  foldr1 f v (Right x) t = f x v t

  foldMap1 f (Left _)  t = neutral # t
  foldMap1 f (Right x) t = f x t

  traverse1_ f (Left _)  t = t
  traverse1_ f (Right v) t = f v t

-- List and SnocList

export
foldl1List : (a -> e -> F1 s a) -> a -> List e -> F1 s a
foldl1List f v []        t = v # t
foldl1List f v (x :: xs) t = let v2 # t1 := f v x t in foldl1List f v2 xs t1

export
foldr1SnocList : (e -> a -> F1 s a) -> a -> SnocList e -> F1 s a
foldr1SnocList f v [<]       t = v # t
foldr1SnocList f v (sx :< x) t = let v2 # t1 := f x v t in foldr1SnocList f v2 sx t1

export %inline
foldr1List : (e -> a -> F1 s a) -> a -> List e -> F1 s a
foldr1List f v xs = foldr1SnocList f v ([<] <>< xs)

export %inline
foldl1SnocList : (a -> e -> F1 s a) -> a -> SnocList e -> F1 s a
foldl1SnocList f v sx = foldl1List f v (sx <>> [])

export
foldMap1List : Monoid m => (a -> F1 s m) -> List a -> F1 s m
foldMap1List f = go neutral
  where
    go : m -> List a -> F1 s m
    go v []        t = v # t
    go v (x :: xs) t = let w # t1 := f x t in go (v <+> w) xs t1

export
foldMap1SnocList : Monoid m => (a -> F1 s m) -> SnocList a -> F1 s m
foldMap1SnocList f = go neutral
  where
    go : m -> SnocList a -> F1 s m
    go v [<]       t = v # t
    go v (sx :< x) t = let w # t1 := f x t in go (w <+> v) sx t1

export
traverse1_List : (a -> F1' s) -> List a -> F1' s
traverse1_List f []        t = t
traverse1_List f (x :: xs) t = traverse1_List f xs (f x t)

export
traverse1_SnocList : (a -> F1' s) -> SnocList a -> F1' s
traverse1_SnocList f [<]       t = t
traverse1_SnocList f (sx :< x) t = traverse1_SnocList f sx (f x t)

export %inline
Foldable1 List where
  foldl1     = foldl1List
  foldr1     = foldr1List
  foldMap1   = foldMap1List
  traverse1_ = traverse1_List

export %inline
Foldable1 SnocList where
  foldl1     = foldl1SnocList
  foldr1     = foldr1SnocList
  foldMap1   = foldMap1SnocList
  traverse1_ = traverse1_SnocList

export
foldl1Vect : (a -> e -> F1 s a) -> a -> Vect n e -> F1 s a
foldl1Vect f v []        t = v # t
foldl1Vect f v (x :: xs) t = let v2 # t1 := f v x t in foldl1Vect f v2 xs t1

ontoSnocList : SnocList a -> Vect n a -> SnocList a
ontoSnocList sx []      = sx
ontoSnocList sx (x::xs) = ontoSnocList (sx :< x) xs

export
foldr1Vect : (e -> a -> F1 s a) -> a -> Vect n e -> F1 s a
foldr1Vect f v xs = foldr1SnocList f v (ontoSnocList [<] xs)

export
foldMap1Vect : Monoid m => (a -> F1 s m) -> Vect n a -> F1 s m
foldMap1Vect f = go neutral
  where
    go : m -> Vect k a -> F1 s m
    go v []        t = v # t
    go v (x :: xs) t = let w # t1 := f x t in go (v <+> w) xs t1

export
traverse1_Vect : (a -> F1' s) -> Vect n a -> F1' s
traverse1_Vect f []        t = t
traverse1_Vect f (x :: xs) t = traverse1_Vect f xs (f x t)

export %inline
Foldable1 (Vect n) where
  foldl1     = foldl1Vect
  foldr1     = foldr1Vect
  foldMap1   = foldMap1Vect
  traverse1_ = traverse1_Vect

export %inline
Foldable1 List1 where
  foldl1 f v   = foldl1List f v . forget
  foldr1 f v   = foldr1List f v . forget
  foldMap1 f   = foldMap1List f . forget
  traverse1_ f = traverse1_List f . forget

--------------------------------------------------------------------------------
-- Traversable1
--------------------------------------------------------------------------------

public export
interface Foldable1 f => Traversable1 f where
  traverse1 : (a -> F1 s b) -> f a -> F1 s (f b)

export
Traversable1 Maybe where
  traverse1 f Nothing  t = Nothing # t
  traverse1 f (Just v) t = let w # t1 := f v t in Just w # t1

export
Traversable1 (Either e) where
  traverse1 f (Left v)  t = Left v # t
  traverse1 f (Right v) t = let w # t1 := f v t in Right w # t1

export
traverse1List : SnocList b -> (a -> F1 s b) -> List a -> F1 s (List b)
traverse1List sx f []        t = (sx <>> []) # t
traverse1List sx f (x :: xs) t =
  let v # t1 := f x t
   in traverse1List (sx :< v) f xs t1

export
traverse1SnocList : List b -> (a -> F1 s b) -> SnocList a -> F1 s (SnocList b)
traverse1SnocList xs f [<]       t = ([<] <>< xs) # t
traverse1SnocList xs f (sx :< x) t =
  let v # t1 := f x t
   in traverse1SnocList (v::xs) f sx t1

ontoVect : (sx : SnocList a) -> Vect n a -> Vect (length sx + n) a

export
traverse1Vect :
     (sx : SnocList b)
  -> (a -> F1 s b)
  -> Vect n a
  -> F1 s (Vect (length sx + n) b)
traverse1Vect           sx f []        t = ontoVect sx [] # t
traverse1Vect {n = S k} sx f (x :: xs) t =
  let Token.(#) v t1 := f x t
   in rewrite sym (plusSuccRightSucc (length sx) k)
      in traverse1Vect (sx :< v) f xs t1

export %inline
Traversable1 List where
  traverse1 = traverse1List [<]

export %inline
Traversable1 SnocList where
  traverse1 = traverse1SnocList []

export %inline
Traversable1 (Vect n) where
  traverse1 = traverse1Vect [<]

export
Traversable1 List1 where
  traverse1 f (x:::xs) t =
    let w  # t1 := f x t
        wx # t2 := traverse1 f xs t1
     in (w ::: wx) # t2
