module Atomically

import Data.Vect as V
import Data.Linear.Ref1
import System.Concurrency
import System

%default total

public export
ITER : Nat
ITER = 1_000_000

data Prog = Unsafe | CAS | Mut

inc : (r : Ref s Nat) -> F1' s
inc r = mod1 r S

casinc : (r : Ref s Nat) -> F1' s
casinc r = casmod1 r S

atomicallyinc : Mutex -> IORef Nat -> Nat -> IO ()
atomicallyinc m r 0     = pure ()
atomicallyinc m r (S k) = do
  () <- runIO $ \t =>
    atomically r m S t
  atomicallyinc m r k

prog : Prog -> Mutex -> IORef Nat -> IO ()
prog Unsafe m ref = runIO (forN ITER $ inc ref)
prog CAS    m ref = runIO (forN ITER $ casinc ref)
prog Mut    m ref = atomicallyinc m ref ITER

runProg : Prog -> Nat -> IO Nat
runProg prg n = do
  mut <- makeMutex
  ref <- newref Z
  ts  <- sequence $ V.replicate n (fork $ prog prg mut ref)
  traverse_ (\t => threadWait t) ts
  runIO (read1 ref)

main : IO ()
main = do
  u <- runProg Unsafe 4
  c <- runProg CAS 4
  m <- runProg Mut 4
  when (u >= c) (die "no race condition")
  when (c /= 4 * ITER) (die "CAS synchronization failed")
  when (m /= 4 * ITER) (die "atomically failed")
  putStrLn "Atomically counter succeeded!"
