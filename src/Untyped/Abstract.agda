module Untyped.Abstract where

open import Function

open import Data.String
open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.Sum as Sum
open import Data.Maybe
open import Strict

open import Debug.Trace
open import Category.Monad

open import Untyped.Monads

postulate fail : ∀ {a : Set} → a

willneverhappenipromise : ∀ {a : Set} → String → a
willneverhappenipromise m = trace m fail

module _ where

  Var  = ℕ
  Chan = ℕ

  mutual
    record Closure : Set where
      inductive
      constructor ⟨_⊢_⟩
      field
        env  : Env
        body : Exp

    data Val : Set where
      tt    : Val
      nat   : ℕ → Val
      chan  : Chan → Val
      ⟨_,_⟩ : Val → Val → Val -- pairs
      clos  : Closure → Val -- closures

    Env = List Val

    data Exp : Set where
      -- the functional core
      nat     : ℕ → Exp
      var     : Var → Exp
      ƛ       : Exp → Exp
      _·_     : Exp → Exp → Exp

      -- products
      pair    : Exp → Exp → Exp
      letp    : Exp → Exp → Exp

      -- communication
      close   : Exp → Exp
      receive : Exp → Exp
      send    : (ch : Exp) → (v : Exp) → Exp

      -- threading
      fork    : Exp → Exp

  extend  : Val → Env → Env
  extend = _∷_

  unsafeLookup : ∀ {a} → ℕ → List a → a
  unsafeLookup _ [] = willneverhappenipromise "lookup fail"
  unsafeLookup zero (x ∷ xs)    = x
  unsafeLookup (suc n) (x ∷ xs) = unsafeLookup n xs

  unsafeUpdate : ∀ {a} → ℕ → List a → a → List a
  unsafeUpdate n [] a = willneverhappenipromise "update fail"
  unsafeUpdate zero (x ∷ xs) a = a ∷ xs
  unsafeUpdate (suc n) (x ∷ xs) a = x ∷ unsafeUpdate n xs a

  -- Ideally this should be two different dispatch sets
  data Comm : Set where
    -- communication
    send  : Chan → Val → Comm
    recv  : Chan → Comm
    clos  : Chan → Comm

  data Threading : Set where
    -- threading
    fork  : Closure → Threading
    yield : Threading

  Cmd = Comm ⊎ Threading

  ⟦_⟧-comm : Comm → Set
  ⟦ clos x ⟧-comm = ⊤
  ⟦ send x x₁ ⟧-comm = ⊤
  ⟦ recv x ⟧-comm = Val

  ⟦_⟧-thr : Threading → Set
  ⟦ fork x ⟧-thr = Chan
  ⟦ yield ⟧-thr  = ⊤

  ⟦_⟧ : Cmd → Set
  ⟦ inj₁ x ⟧ = ⟦ x ⟧-comm
  ⟦ inj₂ y ⟧ = ⟦ y ⟧-thr

  data Thread : Set where
    thread : Free Cmd ⟦_⟧ Val → Thread

  ThreadPool = List Thread

  Links  = Chan → Chan

  data Blocked : Set where
    blocked : Blocked
      
  {- Free an expression from its earthly -}
  module _ {m}
    ⦃ m-monad : RawMonad m ⦄
    ⦃ m-read  : MonadReader m Env ⦄
    ⦃ m-res   : MonadResumption m Closure Chan ⦄
    ⦃ m-comm  : MonadComm m Chan Val ⦄
    where

    open M

    {-# NON_TERMINATING #-}
    eval : Exp → m Val
    eval (nat n) = do
      return (nat n)
    eval (var x) = do
      asks (unsafeLookup (trace "resolve var" x)) 
    eval (ƛ e) = do
      asks (clos ∘ ⟨_⊢ e ⟩)
    eval (f · e) = do
      clos ⟨ env ⊢ body ⟩ ← eval f
        where _ → willneverhappenipromise "not a closure"
      v ← eval e
      local (λ _ → extend v env) (eval body)

    -- products
    eval (pair e₁ e₂) = do
      v₁ ← eval e₁
      v₂ ← eval e₂
      return ⟨ v₁ , v₂ ⟩
      
    eval (letp b e) = do
      ⟨ v₁ , v₂ ⟩ ← eval b
        where _ → willneverhappenipromise "not a pair"
      local (extend v₂ ∘ extend v₁) $ eval e

    -- communication
    eval (close e) = do
      chan c ← eval e
        where _ → willneverhappenipromise "not a channel to close"
      M.close c
      return tt
    eval (receive e) = do
      chan c ← eval e
        where _ → willneverhappenipromise "not a channel to receive on"
      M.recv c
    eval (send e₁ e₂) = do
      chan c ← eval e₁
        where _ → willneverhappenipromise "not a channel to send on"
      v ← eval e₂
      M.send c v
      return tt

    -- threading
    eval (fork e) = do
      clos cl ← eval e
        where _ → willneverhappenipromise "not a closure to fork"
      c ← M.fork cl
      return (chan c)

  {- Interpreting communication commands -}
  module _ {com}
    ⦃ com-comm  : MonadComm com Chan Val ⦄ where

    communicate : (cmd : Comm) → com ⟦ cmd ⟧-comm
    communicate (Comm.send c v) = trace "sending" $ M.send c v
    communicate (Comm.recv x)   = trace "receiving" $ M.recv x
    communicate (clos x)        = trace "closing" $ M.close x

  {- Interpreting threading commands -}
  module _ {thr}
    ⦃ thr-res   : MonadResumption thr Closure Chan ⦄ where

    threading : (cmd : Threading) → thr ⟦ cmd ⟧-thr
    threading (Threading.fork cl) = trace "forking" $ M.fork cl
    threading Threading.yield     = trace "yielding" $ M.yield

  module _ {cmd}
    ⦃ cmd-comm  : MonadComm cmd Chan Val ⦄
    ⦃ cmd-res   : MonadResumption cmd Closure Chan ⦄ where

    handle : (c : Cmd) → cmd ⟦ c ⟧
    handle = Sum.[ communicate , threading ]

  {- Round robin scheduling -}
  module _ {w : Set} {m}

    ⦃ monad : RawMonad m ⦄
    ⦃ read  : MonadState m (List w) ⦄

    (atomic : w → m ⊤) where

    open M

    {-# NON_TERMINATING #-}
    robin : m ⊤
    robin = do
      (h ∷ tl) ← get
        where [] → return tt
      put tl
      trace "atomics ↓" $ atomic h
      trace "--------- next round ----------" robin
