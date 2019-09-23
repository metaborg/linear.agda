open import Data.List
open import Data.Product
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.Separation

module Relation.Unary.Separation.Monad.State {ℓ} 
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{_ : IsUnitalSep r u}}
  (St : Pred (C × C) ℓ) where

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

-- we are constructing a relative monad over the market resource morphism
open Monads (market C) public
open Morphism (market C) public

State : Pred C ℓ → Pred (Market C) ℓ
State P = ● St ─✴ (J P) ✴ ● St

instance
  M-monad : Monad ⊤ _ (λ _ _ → State)
  app (Monad.return M-monad px) st σ₂ = (inj px ×⟨ σ₂ ⟩ st )
  app (app (Monad.bind M-monad {Q = Q} f) m σ₁) st σ₂ with ⊎-assoc σ₁ σ₂
  ... | _ , σ₃ , σ₄ with app m st σ₄
  app (app (Monad.bind M-monad {Q = Q} f) m σ₁) st σ₂ | _ , offerᵣ σ , σ₄ | inj px ×⟨ offerᵣ σ₅ ⟩ st' with ⊎-unassoc σ₅ σ 
  ... | _ , τ₁ , τ₂ = let mq = app f px (⊎-comm τ₁) in app mq st' (offerᵣ τ₂)
