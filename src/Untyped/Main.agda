module Untyped.Main where

open import Function

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.Sum
open import Category.Monad

open import Strict

open import Untyped.Monads
open import Untyped.Abstract

open M

-- the monad in which we interpret expressions into command trees
M : Set → Set
M = ReaderT Env (Free Cmd ⟦_⟧)

record ServerState : Set where
  constructor server
  field
    threads : ThreadPool
    nextChan : ℕ
    links   : List ℕ
    queues  : List (List Val)

empty : ServerState
empty = record { threads = []; links = []; queues = []; nextChan = 0 }

SchedM : Set → Set
SchedM = StateT ServerState id

SchedM? : Set → Set
SchedM? = ExceptT Blocked (StateT ServerState id)

instance
  free-monad' = free-monad

  {- The monad that interprets expressions into threads -}
  m-monad : RawMonad M
  m-monad = reader-monad Env (Free Cmd ⟦_⟧) ⦃ free-monad ⦄
      
  m-reader : MonadReader M Env
  m-reader = record
    { ask   = Free.pure
    ; local = λ f c E → c (f E) }

  m-comm : MonadComm M Chan Val
  m-comm = record
    { recv = λ c E   → impure (inj₁ (Comm.recv c)) Free.pure
    ; send = λ c v E → impure (inj₁ (Comm.send c v)) Free.pure
    ; close = λ c E  → impure (inj₁ (Comm.clos c)) Free.pure }

  m-res  : MonadResumption M Closure Chan
  m-res  = record
    { yield = λ _      → impure (inj₂ Threading.yield) Free.pure
    ; fork  = λ clos _ → impure (inj₂ (Threading.fork clos)) Free.pure }

  {- The monad that executes threads -}

  s-monad : RawMonad SchedM
  s-monad = state-monad ServerState id ⦃ id-monad ⦄

  s-state : MonadState SchedM ServerState
  s-state = state-monad-state ServerState id ⦃ id-monad ⦄

  s-thread-state : MonadState SchedM ThreadPool
  s-thread-state = focus-monad-state
    ServerState.threads
    (λ thr s → record s { threads = thr })
    s-state

  s-writer : MonadWriter SchedM ThreadPool
  s-writer = record
    { write = λ pool → do
            modify λ st → record st { threads = ServerState.threads st ++ pool }
            return tt
    }

  s?-monad : RawMonad SchedM?
  s?-monad = except-monad

  s?-monad-except : MonadExcept SchedM? Blocked
  s?-monad-except = except-monad-except

newChan : SchedM (Chan × Chan)
newChan = do
  c ← gets ServerState.nextChan
  let left  = c
  let right = c + 1
  modify (λ st → record st
    { nextChan = c + 2
    ; links   = ServerState.links st ++ (right ∷ left ∷ [])
    ; queues  = ServerState.queues st ++ ([] ∷ [] ∷ []) })
  return (left , right)

instance
  s-comm : MonadComm SchedM? ℕ Val
  s-comm = record
    { recv  = λ ch → do
                queue ← gets (unsafeLookup ch ∘ ServerState.queues)
                case queue of λ where
                  []       → throw blocked
                  (x ∷ xs) → do
                    modify λ st →
                      (record st { queues = unsafeUpdate ch (ServerState.queues st) xs})
                    return x
    ; send  = λ ch v → do
                ch⁻¹  ← gets (unsafeLookup ch ∘ ServerState.links)
                queue ← gets (unsafeLookup ch⁻¹ ∘ ServerState.queues)
                modify λ st →
                  record st { queues = unsafeUpdate ch⁻¹ (ServerState.queues st) (queue ∷ʳ v) }
                return tt
    ; close = λ ch → do
                return tt
    }

  s-res : MonadResumption SchedM? Closure Chan
  s-res = record
    { yield = return tt
    ; fork  = λ where
      ⟨ env ⊢ e ⟩ →
        do
          (l , r) ← newChan
          schedule [ thread $ eval ⦃ m-monad ⦄ e (extend (chan l) env) ]
          return r
    }

handler : (c : Cmd) → Cont Cmd ⟦_⟧ c Val → SchedM ⊤
handler c k s =
  let (s' , r) = handle {SchedM?} c s in
  case r of λ where
    (exc e) → schedule [ thread (impure c k) ] s' -- reschedule
    (✓ v)   → schedule [ thread (k v) ] s'

atomic : Thread → SchedM ⊤
atomic (thread (Free.pure x))  = return tt
atomic (thread (impure cmd x)) = handler cmd x

run : Exp → ℕ
run e =
  let
    main = thread $ eval e []
    (s , v) = robin ⦃ s-monad ⦄ atomic (record empty { threads = [ main ]})
  in case (ServerState.threads s) of λ where
    [] → 0
    _  → 1
    

example : Exp
example =
  let
    slave  = ƛ (Exp.send (var 0) (nat 3))
    master = Exp.receive (Exp.fork slave) 
  in master

import IO

main = do
  let val = run example 
  case val of λ where
    0 → IO.run (IO.putStrLn "done!")
    _ → IO.run (IO.putStrLn "?!")

