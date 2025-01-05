module Concurrent

import Data.Vect as V
import Data.Linear.Ref1
import System.Concurrency
import System

%default total

ITER : Nat
ITER = 1_000_000

data Prog = Unsafe | CAS | Mut

inc : (r : IORef Nat) -> F1' [World]
inc r = mod1 r S

casinc : (r : IORef Nat) -> F1' [World]
casinc r = casmod1 r S

mutinc : Mutex -> IORef Nat -> Nat -> IO ()
mutinc m r 0     = pure ()
mutinc m r (S k) = do
  mutexAcquire m
  runIO (inc r)
  mutexRelease m
  mutinc m r k

prog : Prog -> Mutex -> IORef Nat -> IO ()
prog Unsafe m ref = runIO (forN ITER $ inc ref)
prog CAS    m ref = runIO (forN ITER $ casinc ref)
prog Mut    m ref = mutinc m ref ITER

toProg : List String -> (Prog,Nat)
toProg [_,"CAS",   n] = (CAS, cast n)
toProg [_,"mut",   n] = (Mut, cast n)
toProg [_,"unsafe",n] = (Unsafe, cast n)
toProg _              = (Unsafe, 4)

main : IO ()
main = do
  (prg,n) <- toProg <$> getArgs
  mut     <- makeMutex
  ref     <- newIORef Z
  ts      <- sequence $ V.replicate n (fork $ prog prg mut ref)
  traverse_ (\t => threadWait t) ts
  n       <- runIO (read1 ref)
  printLn n
