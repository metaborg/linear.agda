module Untyped.Monads where

open import Function

open import Data.Unit
open import Data.Product as Prod
open import Data.Sum
open import Data.Sum public using () renaming (_⊎_ to Exceptional; inj₁ to exc; inj₂ to ✓)

open import Category.Monad

id-monad : ∀ {ℓ} → RawMonad {ℓ} id
id-monad = record
  { return = id
  ; _>>=_  = λ a f → f a }

record MonadReader (m : Set → Set) (e : Set) : Set₁ where
  field
    ask       : m e
    local     : ∀ {a} → (e → e) → m a → m a

  asks : ∀ ⦃ _ : RawMonad m ⦄ {a} → (e → a) → m a
  asks ⦃ m ⦄ f = let open RawMonad m in do
    e ← ask
    return $ f (e)

ReaderT : Set → (M : Set → Set) → Set → Set
ReaderT E M A = E → M A

module _ (E : Set) (M : Set → Set) ⦃ mon : RawMonad M ⦄ where
  open RawMonad mon

  reader-monad : RawMonad (ReaderT E M) 
  reader-monad = record
    { return = const ∘ return 
    ; _>>=_  = λ m f e → m e >>= λ x → f x e }

  reader-monad-reader : MonadReader (ReaderT E M) E
  reader-monad-reader = record
    { ask = return
    ; local = λ f c e → c (f e) }

record MonadWriter (m : Set → Set) (w : Set) : Set₁ where
  field
    write : w → m ⊤

record MonadState (m : Set → Set) (s : Set) : Set₁ where
  field
    state : ∀ {a} → (s → s × a) → m a

  put : s → m ⊤
  put s = state λ _ → (s , tt)

  get : m s
  get = state λ s → (s , s)

  gets : ∀ {a} → (s → a) → m a
  gets f = state λ s → (s , f s)

  modify : ⦃ _ : RawMonad m ⦄ → (s → s) → m ⊤
  modify ⦃ M ⦄ f = let open RawMonad M in do
    s ← get
    put (f s)

StateT : Set → (M : Set → Set) → Set → Set
StateT S M A = S → M (S × A)

module _ (S : Set) (M : Set → Set) ⦃ mon : RawMonad M ⦄ where

  state-monad : RawMonad (StateT S M) 
  state-monad = record
    { return = λ a s → return (s , a)
    ; _>>=_  = λ m f s → m s >>= λ where (s' , a) → f a s' }
    where open RawMonad mon

  state-monad-state : MonadState (StateT S M) S
  state-monad-state = record
    { state = λ f s → return (f s) }
    where open RawMonad mon

  open MonadState state-monad-state

{- State focussing -}
module _ {S F M} (focus : S → F) (update : F → S → S)
  ⦃ mon : RawMonad M ⦄
  (st  : MonadState M S)
  where

  focus-monad-state : MonadState M F
  focus-monad-state = record
    { state = λ f →
      MonadState.state st λ s →
        Prod.map₁ (λ f → update f s) (f (focus s))
    }

module _ {M S} ⦃ m : RawMonad M ⦄ (stm : MonadState M S) where
  open RawMonad m
  open MonadState stm

  state-monad-reader : MonadReader M S
  state-monad-reader = record
    { ask   = get
    ; local = λ f m → do
      backup ← get
      modify f
      a ← m
      put backup
      return a
    }

  state-monad-writer : MonadWriter M S
  state-monad-writer = record
    { write = put }

ExceptT : Set → (Set → Set) → Set → Set
ExceptT E M A = M (E ⊎ A)

record MonadExcept (m : Set → Set) (e : Set) : Set₁ where
  field
    throw     : ∀ {a} → e → m a

module _ {E : Set} {M : Set → Set} ⦃ mon : RawMonad M ⦄ where
  open RawMonad mon

  except-monad : RawMonad (ExceptT E M)
  except-monad = record
    { return = λ a → return (✓ a)
    ; _>>=_ = λ where
                c f → c >>= λ where
                  (exc x) → return $ exc x
                  (✓ y)   → f y }

  except-monad-except : MonadExcept (ExceptT E M) E
  except-monad-except = record
    { throw = λ e → return (exc e) }

record MonadResumption (m : Set → Set) (c h : Set) : Set₁ where
  field
    yield : m ⊤
    fork  : c → m h

record MonadComm (m : Set → Set) (c v : Set) : Set₁ where
  field
    recv  : c → m v
    send  : c → v → m ⊤
    close : c → m ⊤

module _ c (r : c → Set) where
  mutual
    Cont = λ cmd a → (r cmd → Free a)

    data Free a : Set where
      pure   : a → Free a
      impure : (cmd : c) → Cont cmd a → Free a

free-monad : ∀ {c r} → RawMonad (Free c r)
free-monad = record
  { return = pure
  ; _>>=_  = bind }
  where
    bind : ∀ {c r a b} → Free c r a → (a → Free c r b) → Free c r b
    bind = λ where
      (pure a) f     → f a
      (impure c k) f → impure c (flip bind f ∘ k)

-- one cannot easily define instances like free-monad-comm generically
-- for some command type and interpretation, because MonadComm
-- requires that the recv return type is fixed a priori, whereas
-- free allows it to be dependent on the command payload.

module M where
  open RawMonad ⦃...⦄ public
  open MonadReader ⦃...⦄ public
  open MonadWriter ⦃...⦄ public renaming (write to schedule)
  open MonadResumption ⦃...⦄ public
  open MonadComm ⦃...⦄ public
  open MonadExcept ⦃...⦄ public
  open MonadState ⦃...⦄ public
