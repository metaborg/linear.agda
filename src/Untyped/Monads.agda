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

module M where
  open RawMonad ⦃...⦄ public
  open MonadReader ⦃...⦄ public
  open MonadWriter ⦃...⦄ public renaming (write to schedule)
  open MonadResumption ⦃...⦄ public
  open MonadComm ⦃...⦄ public
  open MonadExcept ⦃...⦄ public
  open MonadState ⦃...⦄ public
