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
M a = ReaderT Env (Free Cmd ⟦_⟧) a

SchedM : Set → Set
SchedM a = {!!}

instance
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

  m-res  : MonadResumption M Closure
  m-res  = record
    { yield = λ _      → impure (inj₂ Threading.yield) Free.pure
    ; fork  = λ clos _ → impure (inj₂ (Threading.fork clos)) Free.pure }

  {- The monad that executes threads -}
  s-monad : RawMonad SchedM
  s-monad = {!!}

  s-writer : MonadWriter SchedM ThreadPool
  s-writer = {!!}

  s-reader : MonadReader SchedM ThreadPool
  s-reader = {!!}

run : Exp → ⊤
run e =
  let tree = (eval ⦃ m-monad ⦄ e [])
  in {!!} -- M.runReader (loop ? ? ?) [ tree ]
