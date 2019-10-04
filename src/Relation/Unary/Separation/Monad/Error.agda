open import Relation.Unary
open import Relation.Unary.Separation

module Relation.Unary.Separation.Monad.Error {ℓ} {A : Set ℓ}
  {{r : RawSep A}}
  {u} {{_ : IsUnitalSep r u}}
  where

open import Level
open import Function
open import Data.Unit
open import Data.Sum
open import Relation.Unary renaming (U to True)
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Binary.PropositionalEquality

Err : PT A A ℓ ℓ
Err P = True ∪ P

open Monads {{ bs = record { Carrier = A } }} (id-morph A)

instance
  err-monad : Monad ⊤ ℓ (λ _ _ → Err)
  Monad.return err-monad px = inj₂ px
  app (Monad.bind err-monad f) (inj₁ tt) σ = inj₁ tt
  app (Monad.bind err-monad f) (inj₂ y) σ  = app f y σ

error : ∀ {P} → ∀[ Err P ]
error = inj₁ tt
