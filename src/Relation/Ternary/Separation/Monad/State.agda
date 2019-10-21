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

module _ {ℓ} {C : Set ℓ} {{r : RawSep C}} {u} {{s : IsUnitalSep r u}} where

  open Morphism (market {A = C}) public

  STATET : (M : Pt (Market C) ℓ) → (l r : Pred (C × C) ℓ) → Pt C ℓ
  STATET M St St' P = (● St ─✴ M (J P ✴ ● St')) ∘ demand

  StateT : (M : Pt (Market C) ℓ) → Pred (C × C) ℓ → Pt C ℓ
  StateT M St = STATET M St St

  open import Relation.Ternary.Separation.Monad.Identity

  State : Pred (C × C) ℓ → Pt C ℓ
  State St = STATET Identity.Id St St
  
module StateTransformer {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}}
  (M : Pt (Market C) ℓ)
  {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }}
  {St : Pred (C × C) ℓ}
  where

  instance
    state-monad : Monad ⊤ _ (λ _ _ → StateT M St)
    app (Monad.return state-monad px) st σ₂ = return (inj px ×⟨ σ₂ ⟩ st )
    app (app (Monad.bind state-monad {P = P} {Q = Q} f) m σ₁) st@(lift _ _) σ₂@(offerᵣ σ₅) with ⊎-assoc (demand σ₁) σ₂
    ... | _ , σ₃ , σ₄ = app (bind bound) (app m st σ₄) σ₃
      where
        bound : ((J P ✴ ● St) ─✴ M (J Q ✴ ● St)) (demand _)
        app bound (inj px ×⟨ offerᵣ σ₅ ⟩ st') (offerᵣ σ₆) with ⊎-unassoc σ₅ σ₆
        ... | _ , τ₁ , τ₂ = let mq = app f px (⊎-comm τ₁) in app mq st' (offerᵣ τ₂)

  {- Lift an M computation into a transformed state operation -}
  liftM : ∀ {Φ P} → M P (demand Φ) → StateT M St (P ∘ demand) Φ
  app (liftM mp) (lift μ k) σ@(offerᵣ _) =
    app (mapM′ (wand λ where px σ@(offerₗ _) → inj px ×⟨ ⊎-comm σ ⟩ (lift μ k))) mp (⊎-comm σ)

  {- Lift a state computation into a transformed state operation -}
  liftState : ∀ {P} → ∀[ State St P ⇒ StateT M St P ]
  app (liftState mp) st σ = Monad.return monad (app mp st σ)
 
module StateWithErr {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{s : IsUnitalSep r u}}
  (Exc : Set ℓ) where

  open import Relation.Ternary.Separation.Monad.Error
  open ExceptMonad {A = Market C} Exc public
  open StateTransformer {C = C} (Except Exc) {{ monad = except-monad }} public

  open import Data.Sum

  State? : ∀ (S : Pred (C × C) ℓ) → Pt C ℓ
  State? = StateT (Except Exc)

  recoverWith : ∀ {S P} {M : Pt (Market C) ℓ} {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }}
                → ∀[ (⋂[ _ ∶ Exc ] StateT M S P) ⇒ State? S P ⇒ StateT M S P ]
  app (recoverWith mq mp) μ σ with app mp μ σ
  ... | error e = app (mq e) μ σ
  ... | ✓ px    = return px

  try : ∀ {S P} → ε[ State? S P ] → ε[ State S (Emp ∪ P) ]
  app (try mp?) st σ with app mp? st σ
  ... | error e                = inj (inj₁ empty) ×⟨ σ ⟩ st
  ... | ✓ (inj px ×⟨ σ' ⟩ st') = inj (inj₂ px) ×⟨ σ' ⟩ st'

  raise : ∀ {S P} → Exc → ∀[ State? S P ]
  app (raise {P} e) μ σ = partial (inj₁ e)
