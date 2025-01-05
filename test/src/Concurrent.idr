module Concurrent

import Data.Linear.Ref1
import System.Concurrency
import System

%default total

ITER : Nat
ITER = 10_000_000

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

toProg : List String -> Prog
toProg [_,"CAS"] = CAS
toProg [_,"Mut"] = Mut
toProg _         = Unsafe

main : IO ()
main = do
  prg <- toProg <$> getArgs
  mut <- makeMutex
  ref <- newIORef Z
  t1  <- fork (prog prg mut ref)
  t2  <- fork (prog prg mut ref)
  t3  <- fork (prog prg mut ref)
  t4  <- fork (prog prg mut ref)
  threadWait t1
  threadWait t2
  threadWait t3
  threadWait t4
  n <- runIO (read1 ref)
  printLn n
