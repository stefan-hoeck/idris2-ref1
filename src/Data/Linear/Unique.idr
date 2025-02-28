module Data.Linear.Unique

import public Data.Linear.Token
import Data.Linear.Ref1

%default total

||| A unique identifier in state thread `s`.
|||
||| Every `Token s` generated is guaranteed to be unique.
||| The API of `Token s` consists of only two capabilities:
||| generation of tokens via `token1` and `token`, and a total
||| ordering of tokens of the same state thread.
|||
||| Unique tokens haven am important application as unique identifiers
||| and keys in many applications. We could generate such tokens by
||| threading a pure counter through all computations just as with the
||| state monad. However, in performance sensitive code this could be
||| to hight a price to pay. Therefore, the unique tokens presented
||| here come with far less computational overhead.
|||
||| Implementation detail: Tokens are all generated from a single
||| global mutable counter in a thread-safe manner. However, only
||| tokens of the same state thread can be compared. This makes sure
||| that from an outside view, referential transparency is upheld.
export
record Token (s : Type) where
  constructor T
  value : Nat

export %inline
Eq (Token s) where
  T x == T y = x == y

export %inline
Ord (Token s) where
  compare (T x) (T y) = compare x y

||| Note: This prints the inner value of a `Token s`. Using
|||       `show` on tokens therefore breaks referential transparency.
|||       Only use this for testing and debugging.
export %inline
Show (Token s) where
  show (T v) = show v

||| Returns the internal natural number of a `Token`.
|||
||| Note: This is an implementation detail mainly used for testing.
|||       Consider `Token`s to be opaque values with an `Eq` and
|||       `Ord` implementation. Nothing else. Using this function
|||       breaks referential transparency!
export %inline
unsafeVal : Token s -> Nat
unsafeVal = value

-- Internal mutable token state. This is read and updated
-- via `casupdate1`, which is thread-safe, but currently works
-- only on Chez and JavaScript (and, possibly, Racket).
%noinline
tok_ : Ref s Nat
tok_ = believe_me $ unsafePerformIO $ newref 0

||| Generates a new unique token.
|||
||| This token is unique throughout the lifetime of an application,
||| as it is generated from a single, global, mutable reference.
||| Unique token generation is thread-safe.
export %inline
token1 : F1 s (Token s)
token1 = casupdate1 tok_ (\n => (n+1, T n))

||| Generates a new unique token.
|||
||| This token is unique throughout the lifetime of an application,
||| as it is generated from a single, global, mutable reference.
||| Unique token generation is thread-safe.
export %inline
token : Lift1 s f => f (Token s)
token = lift1 token1
