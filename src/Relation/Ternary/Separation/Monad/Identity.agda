module Relation.Ternary.Separation.Monad.Identity where

open import Level
open import Function
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms

open import Data.Unit
open Monads

module Identity {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{us : IsUnitalSep r u}}
 where

  private
    instance
      c-sep : Separation ℓ
      c-sep = record { Carrier = C }

  Id : ∀ {ℓ} → Pt C ℓ
  Id P = P

  instance
    id-monad : Monad ⊤ ℓ (λ _ _ → Id)
    Monad.return id-monad = id
    app (Monad.bind id-monad f) px = app f px

