module Main

import Data.Linear.Ref1
import Data.Linear.Token.Syntax
import Data.Linear.Traverse1
import Data.List
import Profile

%default total

zipWithIndexRec : List a -> List (Nat,a)
zipWithIndexRec = go [<] 0
  where
    go : SnocList (Nat,a) -> Nat -> List a -> List (Nat,a)
    go sp n []      = sp <>> []
    go sp n (x::xs) = go (sp :< (n,x)) (S n) xs

pairLet : Ref1 () s Nat => a -> F1 s (Nat,a)
pairLet x t =
  let n # t2 := read1 t
      t3     := write1 (S n) t2
   in (n,x) # t3

pairSugar : Ref1 () s Nat => a -> F1 s (Nat,a)
pairSugar v = Syntax.do
  n <- read1
  write1 (S n)
  pure (n,v)

zipWithIndexLet : List a -> List (Nat,a)
zipWithIndexLet xs = withRef1 0 $ traverse1 pairLet xs

zipWithIndexSugar : List a -> List (Nat,a)
zipWithIndexSugar xs = withRef1 0 $ traverse1 pairSugar xs

list : Nat -> List String
list n = List.replicate n "foo"

bench : Benchmark Void
bench = Group "ref1"
  [ Group "zipWithIndex rec"
      [ Single "1"       (basic zipWithIndexRec $ list 1)
      , Single "1000"    (basic zipWithIndexRec $ list 1000)
      , Single "1000000" (basic zipWithIndexRec $ list 1000000)
      ]
  , Group "zipWithIndex let"
      [ Single "1"       (basic zipWithIndexLet $ list 1)
      , Single "1000"    (basic zipWithIndexLet $ list 1000)
      , Single "1000000" (basic zipWithIndexLet $ list 1000000)
      ]
  , Group "zipWithIndex sugar"
      [ Single "1"       (basic zipWithIndexSugar $ list 1)
      , Single "1000"    (basic zipWithIndexSugar $ list 1000)
      , Single "1000000" (basic zipWithIndexSugar $ list 1000000)
      ]
  ]

main : IO ()
main = do
  runDefault (const True) Table show bench
  printLn (zipWithIndexRec $ list 10)
  printLn (zipWithIndexLet $ list 10)
  printLn (zipWithIndexSugar $ list 10)
