module Untyped.Monads where

open import Function

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Sum public using () renaming (_⊎_ to Exceptional; inj₁ to exc; inj₂ to ✓)

open import Category.Monad

record MonadWriter (m : Set → Set) (w : Set) : Set₁ where
  field
    writer    : ∀ {a} → a × w → m a
    runWriter : ∀ {a} → m a → a × w

  write : w → m ⊤
  write w = writer (tt , w)

record MonadState (m : Set → Set) (s : Set) : Set₁ where
  field
    put : s → m ⊤
    get : m s
    modify : (s → s) → m ⊤

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

record MonadExcept (m : Set → Set) (e : Set) : Set₁ where
  field
    throw     : ∀ {a} → e → m a

record MonadResumption (m : Set → Set) (c : Set) : Set₁ where
  field
    yield : m ⊤
    fork  : c → m ⊤

record MonadComm (m : Set → Set) (c v : Set) : Set₁ where
  field
    recv  : c → m v
    send  : c → v → m ⊤
    close : c → m ⊤

data Free c (r : c → Set) a : Set where
  pure   : a → Free c r a
  impure : (cmd : c) → (r cmd → Free c r a) → Free c r a

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
