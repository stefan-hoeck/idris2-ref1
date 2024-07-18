module Data.Linear.Token.Syntax

import public Data.List.Quantifiers
import public Data.Linear.Token

%default total

export %inline
pure : a -> F1 s a
pure = (#)

export %inline
(>>=) : {0 rs,ss,ts : _} -> C1 rs ss a -> (a -> C1 ss ts b) -> C1 rs ts b
(>>=) f g t1 = let v # t2 := f t1 in g v t2

export %inline
(>>) : {0 rs,ss,ts : _} -> C1' rs ss -> C1 ss ts b -> C1 rs ts b
(>>) f g t = let t2 := f t in g t2

export %inline
(<*>) : {0 rs,ss,ts : _} -> C1 rs ss (a -> b) -> C1 ss ts a -> C1 rs ts b
(<*>) f g t =
  let fn # t2 := f t
      v  # t3 := g t2
   in fn v # t3

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
data Allocs : (ts : List Type)  -> Type where
  AS : {0 ts : _} -> (vs : HList ts) -> (1 t : T1 (RS vs)) -> Allocs ts

||| Allocates several resources and binds them to a linear token
||| in one go.
export
allocAll : All Alloc ts -> (1 t : T1 []) -> Allocs ts
allocAll []      t = AS [] t
allocAll (f::fs) t =
  let AS vs t2 := allocAll fs t
      A  v  t3 := f t2
   in AS (v::vs) t3

||| Like `run1`, but for linear computations that work with several
||| bound resources at the same time.
export
allocRun1 :
     All Alloc ts
  -> ((vs : HList ts) -> (1 t : T1 (RS vs)) -> R1 [] a)
  -> a
allocRun1 as f = run1 $ \t => let AS vs t := allocAll as t in f vs t
