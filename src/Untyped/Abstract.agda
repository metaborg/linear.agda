module Untyped.Abstract where

open import Function

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.Sum
open import Data.Maybe

open import Category.Monad

open import Untyped.Monads

postulate willneverhappenipromise : ∀ {a : Set} → a

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
      chan  : Chan → Val
      ⟨_,_⟩ : Val → Val → Val -- pairs
      clos  : Closure → Val -- closures

    Env = List Val

    data Exp : Set where
      -- the functional core
      var     : Var → Exp
      ƛ       : Exp → Exp
      _·_     : Exp → Exp → Exp

      -- products
      pair    : Exp → Exp → Exp
      letp    : Exp → Exp → Exp

      -- communication
      close   : Exp → Exp
      receive : Exp → Exp
      send    : Exp → Exp → Exp

      -- threading
      fork    : Exp → Exp

  extend  : Val → Env → Env
  extend = _∷_

  resolve : Var → Env → Val
  resolve _ [] = willneverhappenipromise
  resolve zero (x ∷ xs)    = x
  resolve (suc n) (x ∷ xs) = resolve n xs

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
  ⟦ fork x ⟧-thr = ⊤
  ⟦ yield ⟧-thr  = ⊤

  ⟦_⟧ : Cmd → Set
  ⟦ inj₁ x ⟧ = ⟦ x ⟧-comm
  ⟦ inj₂ y ⟧ = ⟦ y ⟧-thr

  Thread : Set → Set
  Thread a = Free Cmd ⟦_⟧ a

  ThreadPool = List (Thread ⊤)

  Links  = Chan → Chan

  data Blocked : Set where
    blocked : Blocked
      
  {- Free an expression from its earthly -}
  module _ {m}
    ⦃ m-monad : RawMonad m ⦄
    ⦃ m-read  : MonadReader m Env ⦄
    ⦃ m-res   : MonadResumption m Closure ⦄
    ⦃ m-comm  : MonadComm m Chan Val ⦄
    where

    open M

    {-# NON_TERMINATING #-}
    eval : Exp → m Val
    eval (var x) = do
      asks (resolve x) 
    eval (ƛ e) = do
      asks (clos ∘ ⟨_⊢ e ⟩)
    eval (f · e) = do
      clos ⟨ env ⊢ body ⟩ ← eval f
        where _ → willneverhappenipromise
      v ← eval e
      local (extend v) (eval body)

    -- products
    eval (pair e₁ e₂) = do
      v₁ ← eval e₁
      v₂ ← eval e₂
      return ⟨ v₁ , v₂ ⟩
      
    eval (letp b e) = do
      ⟨ v₁ , v₂ ⟩ ← eval b
        where _ → willneverhappenipromise
      local (extend v₂ ∘ extend v₁) $ eval e

    -- communication
    eval (close e) = do
      chan c ← eval e
        where _ → willneverhappenipromise
      M.close c
      return tt
    eval (receive e) = do
      chan c ← eval e
        where _ → willneverhappenipromise
      M.recv c
    eval (send e₁ e₂) = do
      chan c ← eval e₁
        where _ → willneverhappenipromise
      v ← eval e₂
      M.send c v
      return tt

    -- threading
    eval (fork e) = do
      clos cl ← eval e
        where _ → willneverhappenipromise
      M.fork cl
      return tt

  {- Interpreting communication commands -}
  module _ {com}
    ⦃ com-monad : RawMonad com ⦄
    ⦃ com-comm  : MonadComm com Chan Val ⦄ where

    communicate : (cmd : Comm) → com ⟦ cmd ⟧-comm
    communicate (Comm.send c v) = M.send c v
    communicate (Comm.recv x)   = M.recv x
    communicate (clos x)        = M.close x

  {- Interpreting threading commands -}
  module _ {thr}
    ⦃ thr-res   : MonadResumption thr Closure ⦄ where

    threading : (cmd : Threading) → thr ⟦ cmd ⟧-thr
    threading (Threading.fork cl) = M.fork cl
    threading Threading.yield     = M.yield

  {- Convert a command tree into a -}
  module _ {cmd : Set} {m}
    (interp : cmd → Set)

    ⦃ monad : RawMonad m ⦄
    ⦃ write : MonadWriter m (List (Free cmd interp ⊤)) ⦄

    (handle : (cmd : cmd) → m (interp cmd)) where
    open M

    par : Free cmd interp ⊤ → m ⊤
    par (pure x)       = return x
    par (impure cmd k) = do
      r ← handle cmd
      schedule [ k r ] 

  {- Round robin scheduling -}
  module _ {w : Set} {m}

    ⦃ s-monad : RawMonad m ⦄
    ⦃ s-read  : MonadReader m (List w) ⦄

    (atomic : w → List w) where

    open M

    {-# NON_TERMINATING #-}
    robin : m ⊤
    robin = do
      (h ∷ tl) ← ask
        where [] → return tt
      local (_++ atomic h) robin
