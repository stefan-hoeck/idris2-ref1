module Traverse1

import Data.Linear.Ref1
import Data.Linear.Traverse1
import Derive.Prelude
import Hedgehog

%default total
%language ElabReflection

data Lst : Type -> Type where
  Nil  : Lst a
  (::) : a -> Lst a -> Lst a

Cast (Lst a) (List a) where
  cast Nil = Nil
  cast (x::xs) = x :: cast xs

Cast (List a) (Lst a) where
  cast Nil = Nil
  cast (x::xs) = x :: cast xs

Foldable1 Lst where
  foldl1 f v []       t = v # t
  foldl1 f v (x :: y) t = let v2 # t := f v x t in foldl1 f v2 y t

record FoldRes a where
  constructor FR
  result : a
  events : SnocList Bits8

%runElab derive "FoldRes" [Show,Eq]

testFoldr1 : Foldable1 f => f Bits8 -> FoldRes (List Bits8)
testFoldr1 f =
  run1 $ \t =>
   let ref # t := ref1 [<] t
       vs  # t := Traverse1.foldr1 (\el,a,t => let _ # t := mod1 ref (:<el) t in (el::a) # t) Prelude.Nil f t
       sv  # t := read1 ref t
    in FR vs sv # t

testFoldl1 : Foldable1 f => f Bits8 -> FoldRes (List Bits8)
testFoldl1 f =
  run1 $ \t =>
   let ref # t := ref1 [<] t
       vs  # t := Traverse1.foldl1 (\a,el,t => let _ # t := mod1 ref (:<el) t in (el::a) # t) Prelude.Nil f t
       sv  # t := read1 ref t
    in FR vs sv # t

l1 : Bits8 -> List Bits8
l1 = pure

testFoldMap1 : Foldable1 f => f Bits8 -> FoldRes (List Bits8)
testFoldMap1 f =
  run1 $ \t =>
   let ref # t := ref1 [<] t
       vs  # t := Traverse1.foldMap1 (\el,t => let _ # t := mod1 ref (:<el) t in l1 el # t) f t
       sv  # t := read1 ref t
    in FR vs sv # t

testTraverse1 : Foldable1 f => f Bits8 -> FoldRes ()
testTraverse1 f =
  run1 $ \t =>
   let ref # t := ref1 [<] t
       _   # t := Traverse1.traverse1_ (\el => mod1 ref (:<el)) f t
       sv  # t := read1 ref t
    in FR () sv # t

prop_foldr1 : Property
prop_foldr1 =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testFoldr1 vs === testFoldr1 (cast {to = Lst Bits8} vs)

prop_foldr1List : Property
prop_foldr1List =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testFoldr1 vs === FR vs ([<] <>< reverse vs)

prop_foldl1 : Property
prop_foldl1 =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testFoldl1 vs === testFoldl1 (cast {to = Lst Bits8} vs)

prop_foldl1List : Property
prop_foldl1List =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testFoldl1 vs === FR (reverse vs) ([<] <>< vs)

prop_foldMap1 : Property
prop_foldMap1 =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testFoldMap1 vs === testFoldMap1 (cast {to = Lst Bits8} vs)

prop_foldMap1List : Property
prop_foldMap1List =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testFoldMap1 vs === FR vs ([<] <>< vs)

prop_traverse1 : Property
prop_traverse1 =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testTraverse1 vs === testTraverse1 (cast {to = Lst Bits8} vs)

prop_traverse1List : Property
prop_traverse1List =
  property $ do
    vs <- forAll $ list (linear 0 10) anyBits8
    testTraverse1 vs === FR () ([<] <>< vs)

export
props : Group
props =
  MkGroup "Data.Linear.Traverse1"
    [ ("prop_foldr1List", prop_foldr1List)
    , ("prop_foldr1", prop_foldr1)
    , ("prop_foldl1List", prop_foldl1List)
    , ("prop_foldl1", prop_foldl1)
    , ("prop_foldMap1List", prop_foldMap1List)
    , ("prop_foldMap1", prop_foldMap1)
    , ("prop_traverse1List", prop_traverse1List)
    , ("prop_traverse1", prop_traverse1)
    ]
