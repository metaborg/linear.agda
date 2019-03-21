module Untyped where

open import Function

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.Sum

open import Category.Monad

open import Untyped.Monads
open import Untyped.Abstract

open M

-- TODOS
-- ∘ who is responsible for 'yielding'? The sequence operator of the expression monad or
--   the eval definition? Or the implementation m-comm?

-- the monad in which we interpret expressions into command trees
M : Set → Set
M = ReaderT Env (Free Cmd ⟦_⟧)

record ServerState : Set where
  field
    threads : ThreadPool
    maxChan : ℕ
    links   : List ℕ
    queues  : List (List Val)

empty : ServerState
empty = record { threads = []; links = []; queues = []; maxChan = 0 }

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
  s-writer = state-monad-writer s-thread-state

  s?-monad : RawMonad SchedM?
  s?-monad = except-monad

  s?-monad-except : MonadExcept SchedM? Blocked
  s?-monad-except = except-monad-except

newChan : SchedM (Chan × Chan)
newChan = do
  c ← gets ServerState.maxChan
  modify λ st → record st { maxChan = c + 2 }
  return (c + 1 , c + 2)

newThread : Thread ⊤ → SchedM ⊤
newThread th = do
  modify λ st → record st { threads = ServerState.threads st ∷ʳ th }

instance
  s-comm : MonadComm SchedM? ℕ Val
  s-comm = record
    { recv  = λ ch → do
                {!!}
    ; send  = λ ch v → do
                {!!}
    ; close = λ ch → do
                {!!}
    }

  s-res : MonadResumption SchedM? Closure Chan
  s-res = record
    { yield = return tt
    ; fork  = λ where
      ⟨ env ⊢ e ⟩ → do
        (l , r) ← newChan
        let thread = eval ⦃ m-monad ⦄ e (extend (chan l) env) >>= λ _ → return tt
        newThread thread
        return r }

handler : (c : Cmd) → Cont Cmd ⟦_⟧ c ⊤ → SchedM ⊤
handler c k s =
  let (s' , r) = handle {SchedM?} c s in
  case r of λ where
    (exc e) → schedule [ impure c k ] s' -- reschedule
    (✓ v)   → schedule [ k v ] s'

atomic : Thread ⊤ → SchedM ⊤
atomic (Free.pure x)  = return x
atomic (impure cmd x) = handler cmd x

run : Exp → ⊤
run e =
  let
    tree    = eval e []
    (s , v) = robin ⦃ s-monad ⦄ atomic empty
  in v
