module Relation.Unary.Separation.Monad.Identity where

open import Level
open import Function
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Env

open import Data.Unit

module Identity {ℓ} {{m : MonoidalSep ℓ}} where

  open MonoidalSep m using (Carrier)

  Id : ∀ {ℓ} → Pt Carrier ℓ
  Id P = P

  instance
    id-monad : ∀ {ℓ} → Monad {I = ⊤} {ℓ = ℓ} (λ _ _ → Id)
    Monad.return id-monad = id
    Monad.bind id-monad f px = f px

