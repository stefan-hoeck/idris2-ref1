module Main

import Data.Linear.Ref1
import Syntax.T1
import Hedgehog

%default total

prop_new_read : Property
prop_new_read =
  property $ do
    b8 <- forAll anyBits8
    b8 === withRef1 b8 (\r => read1 r)

prop_write_read : Property
prop_write_read =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    y === withRef1 x (\r,t => let _ # t := write1 r y t in read1 r t)

prop_mod1 : Property
prop_mod1 =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    (x+y) === withRef1 x (\r,t => let _ # t := mod1 r (+y) t in read1 r t)

prop_modandread1 : Property
prop_modandread1 =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    (x+y) === withRef1 x (\r => modAndRead1 r (+y))

prop_readandmod1 : Property
prop_readandmod1 =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    x === withRef1 x (\r => readAndMod1 r (+y))

prop_casupdate1 : Property
prop_casupdate1 =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    x === withRef1 x (\r => casupdate1 r (\v => (v+y,v)))

prop_casmod1 : Property
prop_casmod1 =
  property $ do
    [x,y] <- forAll $ hlist [anyBits8, anyBits8]
    (x+y) === withRef1 x (\r,t => let _ # t := casmod1 r (+y) t in read1 r t)

props : Group
props =
  MkGroup "ref1"
    [ ("prop_new_read", prop_new_read)
    , ("prop_write_read", prop_write_read)
    , ("prop_mod1", prop_mod1)
    , ("prop_modandread1", prop_modandread1)
    , ("prop_readandmod1", prop_readandmod1)
    , ("prop_casupdate1", prop_casupdate1)
    , ("prop_casmod1", prop_casmod1)
    ]

main : IO ()
main = test [props]
