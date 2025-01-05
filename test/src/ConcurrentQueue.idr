module ConcurrentQueue

import Data.Queue
import Data.Vect as V
import Data.Linear.Ref1
import System.Concurrency
import System

%default total

record State where
  constructor ST
  cur   : Nat
  queue : Queue Nat

next : State -> State
next (ST n q) = ST (S n) (enqueue q n)

ITER : Nat
ITER = 10_000

DELAY : Nat
DELAY = 100_000

data Prog = Unsafe | CAS | Mut

inc : (r : IORef State) -> Nat -> F1' [World]
inc r 0     = mod1 r next
inc r (S k) = inc r k

casinc : (r : IORef State) -> Nat -> F1' [World]
casinc r 0     = casmod1 r next
casinc r (S k) = casinc r k

mutinc : Mutex -> IORef State -> Nat -> Nat -> IO ()
mutinc m r n     (S k) = mutinc m r n k
mutinc m r 0     0     = pure ()
mutinc m r (S k) 0     = do
  mutexAcquire m
  runIO (inc r 0)
  mutexRelease m
  mutinc m r k DELAY

prog : Prog -> Mutex -> IORef State -> IO ()
prog Unsafe m ref = runIO (forN ITER $ inc ref DELAY)
prog CAS    m ref = runIO (forN ITER $ casinc ref DELAY)
prog Mut    m ref = mutinc m ref ITER DELAY

toProg : List String -> (Prog,Nat)
toProg [_,"CAS",   n] = (CAS, cast n)
toProg [_,"mut",   n] = (Mut, cast n)
toProg [_,"unsafe",n] = (Unsafe, cast n)
toProg _              = (Unsafe, 4)

main : IO ()
main = do
  (prg,n) <- toProg <$> getArgs
  mut     <- makeMutex
  ref     <- newIORef (ST 0 empty)
  ts      <- sequence $ V.replicate n (fork $ prog prg mut ref)
  traverse_ (\t => threadWait t) ts
  ST n q  <- runIO (read1 ref)
  printLn (length $ toList q)
