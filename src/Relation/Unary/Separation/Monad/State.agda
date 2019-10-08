open import Data.List
open import Data.Product
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.Separation

module Relation.Unary.Separation.Monad.State where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
import Relation.Binary.HeterogeneousEquality as HEq
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad

open import Data.Unit
open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional as I

open Monads

module StateTransformer {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}}
  (M : Pt (Market C) ℓ)
  {{_ : Monads.Monad (id-morph _) ⊤ ℓ (λ _ _ → M) }}
  where

  -- we are constructing a relative monad over the market resource morphism
  open Morphism (market C) public

  STATE : (l r : Pred (C × C) ℓ) → Pred C ℓ → Pred (Market C) ℓ
  STATE St St' P = ● St ─✴ M ((J P) ✴ ● St')

  State : Pred (C × C) ℓ → Pred C ℓ → Pred (Market C) ℓ
  State St = STATE St St

  module _ {St : Pred (C × C) ℓ} where
    instance
      M-monad : Monad (market C) ⊤ _ (λ _ _ → State St)
      app (Monad.return M-monad px) st σ₂ = return (inj px ×⟨ σ₂ ⟩ st )
      app (app (Monad.bind M-monad {P = P} {Q = Q} f) m σ₁) st σ₂ with ⊎-assoc σ₁ σ₂
      ... | _ , σ₃ , σ₄ = app (bind bound) (app m st σ₄) σ₃
        where
          bound : (J P ✴ ● St ─✴ M (J Q ✴ ● St)) (demand _)
          app bound (inj px ×⟨ offerᵣ σ₅ ⟩ st') (offerᵣ σ₆) with ⊎-unassoc σ₅ σ₆
          ... | _ , τ₁ , τ₂ = let mq = app f px (⊎-comm τ₁) in app mq st' (offerᵣ τ₂)

module StateMonad {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}} where

  open import Relation.Unary.Separation.Monad.Identity
  open StateTransformer {C = C} Identity.Id public
