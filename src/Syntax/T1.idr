module Syntax.T1

import public Data.List.Quantifiers
import public Data.Linear.Token

%default total

export %inline
pure : a -> F1 s a
pure = (#)

export %inline
(>>=) :
     (T1 rs -@ Res1 a f)
  -> ((v : a) -> T1 (f v) -@ Res1 b g)
  -> T1 rs
  -@ Res1 b g
(>>=) f g t1 = let v # t2 := f t1 in g v t2

export %inline
(>>) :
     (T1 rs -@ Res1 () f)
  -> (T1 (f ()) -@ Res1 b g)
  -> T1 rs
  -@ Res1 b g
(>>) f g = T1.(>>=) f (\(),t => g t)

export %inline
(<*>) : {0 rs,ss,ts : _} -> C1 rs ss (a -> b) -> C1 ss ts a -> C1 rs ts b
(<*>) f g = T1.do
  fn <- f
  v  <- g
  pure (fn v)

--------------------------------------------------------------------------------
-- Allocating many resources
--------------------------------------------------------------------------------

||| Type alias for an allocator for resources of type `a`.
public export
0 Alloc : Type -> Type
Alloc a = {0 rs : Resources} -> (1 t : T1 rs) -> A1 rs a

||| Computes the resources corresponding to a heterogeneous list
||| of values.
public export
0 RS : HList ts -> Resources
RS []     = []
RS (h::t) = h :: RS t

||| Result of allocating many resources in one go.
|||
||| This pairs as heterogeneous list of resources of types `ts`
||| with a linear token parameterized by those resources.
public export
0 Allocs : (ts : List Type) -> Type
Allocs ts = Res1 (HList ts) RS

||| Allocates several resources and binds them to a linear token
||| in one go.
export
allocAll : All Alloc xs -> (1 t : T1 []) -> Allocs xs
allocAll []      t = [] # t
allocAll (f::fs) t =
  let vs # t := allocAll fs t
      v  # t := f {rs = RS vs} t
   in (v::vs) # t

||| Like `run1`, but for linear computations that work with several
||| bound resources at the same time.
export
allocRun1 :
     All Alloc ts
  -> ((vs : HList ts) -> (1 t : T1 (RS vs)) -> R1 [] a)
  -> a
allocRun1 as f = run1 $ \t => let vs # t := allocAll as t in f vs t
