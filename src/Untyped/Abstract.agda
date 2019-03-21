module Untyped.Abstract where

open import Function

open import Data.Unit
open import Data.Product
open import Data.List
open import Data.Sum

open import Category.Monad

open import Untyped.Monads

postulate willneverhappenipromise : ∀ {a : Set} → a

data Free c (r : c → Set) a : Set where
  pure   : a → Free c r a
  impure : (cmd : c) → (r cmd → Free c r a) → Free c r a

record Sessions : Set₁ where
  field
    Chan : Set
    Var  : Set

module WithSessions (S : Sessions) where
  open Sessions S

  mutual
    record Closure : Set where
      inductive
      constructor ⟨_;_⊢_⟩
      field
        env  : Env
        bind : Var
        body : Exp

    data Val : Set where
      tt    : Val
      chan  : Chan → Val
      ⟨_,_⟩ : Val → Val → Val -- pairs
      clos  : Closure → Val -- closures

    Env = Var → Val

    data Exp : Set where
      -- the functional core
      var     : Var → Exp
      ƛ       : Var → Exp → Exp
      _·_     : Exp → Exp → Exp

      -- products
      pair    : Exp → Exp → Exp
      letp    : Var → Var → Exp → Exp → Exp

      -- communication
      close   : Exp → Exp
      receive : Exp → Exp
      send    : Exp → Exp → Exp

      -- threading
      fork    : Exp → Exp

  resolve : Var → Env → Val
  resolve x f = f x

  postulate
    extend : Var → Val → Env → Env

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
    ⦃ m-read  : MonadReader m (Var → Val) ⦄
    ⦃ m-res   : MonadResumption m Closure ⦄
    ⦃ m-comm  : MonadComm m Chan Val ⦄
    where

    open M

    {-# NON_TERMINATING #-}
    eval : Exp → m Val
    eval (var x) = do
      asks (resolve x) 
    eval (ƛ x e) = do
      asks (clos ∘ ⟨_; x ⊢ e ⟩)
    eval (f · e) = do
      clos ⟨ env ; x ⊢ body ⟩ ← eval f
        where _ → willneverhappenipromise
      v ← eval e
      local (extend x v) (eval body)

    -- products
    eval (pair e₁ e₂) = do
      v₁ ← eval e₁
      v₂ ← eval e₂
      return ⟨ v₁ , v₂ ⟩
      
    eval (letp x y b e) = do
      ⟨ v₁ , v₂ ⟩ ← eval b
        where _ → willneverhappenipromise
      local (extend y v₁ ∘ extend x v₁) $ eval e

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
