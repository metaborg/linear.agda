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
  {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }}
  where

  -- we are constructing a relative monad over the market resource morphism
  open Morphism (market {A = C}) public

  STATE : (l r : Pred (C × C) ℓ) → Pt C ℓ
  STATE St St' P = (● St ─✴ M (J P ✴ ● St')) ∘ demand

  State : Pred (C × C) ℓ → Pt C ℓ
  State St = STATE St St

  module _ {St : Pred (C × C) ℓ} where
    instance
      state-monad : Monad ⊤ _ (λ _ _ → State St)
      app (Monad.return state-monad px) st σ₂ = return (inj px ×⟨ σ₂ ⟩ st )
      app (app (Monad.bind state-monad {P = P} {Q = Q} f) m σ₁) st@(lift _ _) σ₂@(offerᵣ σ₅) with ⊎-assoc (demand σ₁) σ₂
      ... | _ , σ₃ , σ₄ = app (bind bound) (app m st σ₄) σ₃
        where
          bound : ((J P ✴ ● St) ─✴ M (J Q ✴ ● St)) (demand _)
          app bound (inj px ×⟨ offerᵣ σ₅ ⟩ st') (offerᵣ σ₆) with ⊎-unassoc σ₅ σ₆
          ... | _ , τ₁ , τ₂ = let mq = app f px (⊎-comm τ₁) in app mq st' (offerᵣ τ₂)

    liftM : ∀ {Φ P} → M P (demand Φ) → State St (P ∘ demand) Φ
    app (liftM mp) (lift μ k) σ@(offerᵣ _) =
      app (mapM′ (wand λ where px σ@(offerₗ _) → inj px ×⟨ ⊎-comm σ ⟩ (lift μ k))) mp (⊎-comm σ)

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
  (St : Pred (C × C) ℓ)
  (Exc : Set ℓ) where

  open import Relation.Ternary.Separation.Monad.Error
  open ExceptMonad {A = Market C} Exc
  open StateTransformer {C = C} Except {{ monad = err-monad }} public using ()
    renaming (State to State?; state-monad to state?-monad) public

  open import Data.Sum
  open StateMonad

  recoverWith : ∀ {P} → ∀[ (⋂[ _ ∶ Exc ] State St P) ⇒ State? St P ⇒ State St P ]
  app (recoverWith mq mp) μ σ with app mp μ σ
  ... | error e = app (mq e) μ σ
  ... | ✓ px    = px

  try : ∀ {P} → ε[ State? St P ] → ε[ State St (Emp ∪ P) ]
  app (try mp?) st σ with app mp? st σ
  ... | error e                = inj (inj₁ empty) ×⟨ σ ⟩ st
  ... | ✓ (inj px ×⟨ σ' ⟩ st') = inj (inj₂ px) ×⟨ σ' ⟩ st'

  raise : ∀ {P} → Exc → ∀[ State? St P ]
  app (raise {P} e) μ σ = partial (inj₁ e)
