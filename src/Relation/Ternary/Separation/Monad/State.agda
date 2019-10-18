open import Data.List
open import Data.Product
open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Monad.State where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
import Relation.Binary.HeterogeneousEquality as HEq
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Ternary.Separation.Construct.List
open import Relation.Ternary.Separation.Construct.Product
open import Relation.Ternary.Separation.Construct.Market
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad

open import Data.Unit
open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional as I

open Monads

module StateTransformer {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}}
  (M : Pt (Market C) ℓ)
  {{_ : Monads.Monad ⊤ ℓ (λ _ _ → M) }}
  where

  -- we are constructing a relative monad over the market resource morphism
  open Morphism (market {A = C}) public

  STATE : (l r : Pred (C × C) ℓ) → PT C (Market C) ℓ ℓ
  STATE St St' P = ● St ─✴ M (J P ✴ ● St')

  State : Pred (C × C) ℓ → PT C (Market C) ℓ ℓ
  State St = STATE St St

  module _ {St : Pred (C × C) ℓ} where
    instance
      state-monad : Monad ⊤ _ (λ _ _ → State St)
      app (Monad.return state-monad px) st σ₂ = return (inj px ×⟨ σ₂ ⟩ st )
      app (app (Monad.bind state-monad {P = P} {Q = Q} f) m σ₁@(demand _)) st@(lift _ _) σ₂@(offerᵣ σ₅) with ⊎-assoc σ₁ σ₂
      ... | _ , σ₃ , σ₄ = app (bind bound) (app m st σ₄) σ₃
        where
          bound : ((J P ✴ ● St) ─✴ M (J Q ✴ ● St)) (demand _)
          app bound (inj px ×⟨ offerᵣ σ₅ ⟩ st') (offerᵣ σ₆) with ⊎-unassoc σ₅ σ₆
          ... | _ , τ₁ , τ₂ = let mq = app f px (demand (⊎-comm τ₁)) in app mq st' (offerᵣ τ₂)

    liftM : ∀ {P} → ∀[ M (J P) ⇒ State St P ]
    app (liftM mp) μ σ =
      app (mapM′ (wand (λ px σ → px ×⟨ ⊎-comm σ ⟩ μ))) mp (⊎-comm σ)

module StateMonad {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}} where

  open import Relation.Ternary.Separation.Monad.Identity
  open StateTransformer {C = C} Identity.Id {{ Identity.id-monad }} public

  module _
    {St : Pred (C × C) ℓ}
    {M : Pt (Market C) ℓ} {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} where

    {- Lift a state computation into a transformed state operation -}
    liftState : ∀ {P} → ∀[ State St P ⇒ StateTransformer.State M St P ]
    app (liftState mp) st σ = Monad.return monad (app mp st σ)
 
module StateWithErr {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}}
  (St : Pred (C × C) ℓ) where

  open import Relation.Ternary.Separation.Monad.Error
  open StateTransformer {C = C} Err {{ err-monad }} public using ()
    renaming (State to State?; state-monad to state?-monad) public

  open import Data.Sum
  open StateMonad

  recoverWith : ∀ {P} → ∀[ State St P ⇒ State? St P ⇒ State St P ]
  app (recoverWith mq mp) μ σ with app mp μ σ
  ... | error = app mq μ σ
  ... | ✓ px  = px

  try : ∀ {P} → ε[ State? St P ] → ε[ State St (Emp ∪ P) ]
  app (try mp?) st σ with app mp? st σ
  ... | error                  = inj (inj₁ empty) ×⟨ σ ⟩ st
  ... | ✓ (inj px ×⟨ σ' ⟩ st') = inj (inj₂ px) ×⟨ σ' ⟩ st'
