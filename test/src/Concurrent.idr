module Concurrent

import Data.Vect as V
import Data.Linear.Ref1
import System.Concurrency
import System

%default total

public export
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

runProg : Prog -> Nat -> IO Nat
runProg prg n = do
  mut <- makeMutex
  ref <- newIORef Z
  ts  <- sequence $ V.replicate n (fork $ prog prg mut ref)
  traverse_ (\t => threadWait t) ts
  runIO (read1 ref)

main : IO ()
main = do
  u <- runProg Unsafe 4
  c <- runProg CAS 4
  when (u >= c) (die "no race condition")
  when (c /= 4 * ITER) (die "CAS synchronization failed")
  putStrLn "Concurrent counter succeeded!"
