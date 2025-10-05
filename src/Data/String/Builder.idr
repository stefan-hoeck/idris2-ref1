module Data.String.Builder

import Data.Linear.Ref1
import Data.String
import Syntax.T1

%default total

||| A simple mutable string builder based on a snoc list wrapped
||| in a mutable reference.
export
record Builder (q : Type) where
  [noHints]
  constructor B
  ref : Ref q (SnocList String)

||| Creates a new string builder.
export %inline
builder : F1 q (Builder q)
builder = ref1 [<] >>= pure . B

||| Creates a string from a string building function.
export
withBuilder : (forall q . Builder q => F1' q) -> String
withBuilder f =
  run1 $ T1.do
    b <- builder
    f
    ss <- read1 b.ref
    pure (fastConcat $ ss <>> [])

parameters {auto b : Builder q}

  ||| Append a linebreak to the string builder.
  export
  linebreak : F1' q
  linebreak = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<"\n")

  ||| Append a single tab to the string builder.
  export
  tab : F1' q
  tab = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<"\t")

  ||| Append a single space to the string builder.
  export
  space : F1' q
  space = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<" ")

  ||| Append the given number of spaces to the string builder.
  export
  spaces : Nat -> F1' q
  spaces n = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<replicate n ' ')

  ||| Append the given string to the string builder.
  export
  putText : String -> F1' q
  putText "" = pure ()
  putText s  = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<s)

  ||| Append the given string followed by a carriage return
  ||| to the string builder.
  export
  putTextLn : String -> F1' q
  putTextLn "" = linebreak
  putTextLn s  = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<s:<"\n")

  ||| Append the given string followed by a space character return
  ||| to the string builder.
  export
  putTextSep : String -> F1' q
  putTextSep "" = pure ()
  putTextSep s  = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:<s:<" ")

  ||| Appends the given list of characters to the string builder.
  export %inline
  putChars : List Char -> F1' q
  putChars = putText . fastPack

  ||| Append the given list of characters followed by a carriage return
  ||| to the string builder.
  export %inline
  putCharsLn : List Char -> F1' q
  putCharsLn = putTextLn . fastPack

  ||| Show a value and append it to the string builder.
  export %inline
  putShow : Show a => a -> F1' q
  putShow = putText . show

  ||| Show a value and append it to the string builder followed
  ||| by a carriage return.
  export %inline
  putShowLn : Show a => a -> F1' q
  putShowLn = putTextLn . show

  ||| Show a value and append it to the string builder followed
  ||| by a space character.
  export %inline
  putShowSep : Show a => a -> F1' q
  putShowSep = putTextSep . show

  ||| Interpolate a value and append it to the string builder.
  export %inline
  putVal : Interpolation a => a -> F1' q
  putVal = putText . interpolate

  ||| Interpolate a value and append it to the string builder followed
  ||| by a carriage return.
  export %inline
  putValLn : Interpolation a => a -> F1' q
  putValLn = putTextLn . interpolate

  ||| Interpolate a value and append it to the string builder followed
  ||| by a space character.
  export %inline
  putValSep : Interpolation a => a -> F1' q
  putValSep = putTextSep . interpolate

  ||| Append a list of strings to the string builder.
  export %inline
  putAll : List String -> F1' q
  putAll l = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss <>< l)

  ||| Append a string, padding it on the left with the given character.
  export
  putLeftPadded : Nat -> Char -> String -> F1' q
  putLeftPadded n c s = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss :< replicate (n `minus` length s) c :< s)

  ||| Append a string, padding it on the right with the given character.
  export
  padRightPadded : Nat -> Char -> String -> F1' q
  padRightPadded n c s = T1.do
    ss <- read1 b.ref
    write1 b.ref (ss:< s:< replicate (n `minus` length s) c)
