open import Relation.Unary
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Monad.Error {ℓ} {A : Set ℓ}
  {{r : RawSep A}}
  {u} {{_ : IsUnitalSep r u}}
  where

open import Level
open import Function
open import Data.Unit
open import Data.Sum
open import Relation.Unary renaming (U to True)
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Binary.PropositionalEquality

module ExceptTrans
  (M : Pt A ℓ)
  {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} 
  (Exc : Set ℓ) where

  record Except (P : Pred A ℓ) (Φ : A) : Set ℓ where
    constructor partial
    field
      runErr : M ((λ _ → Exc) ∪ P) Φ

  open Except public

  open Monads

  instance
    err-monad : Monad ⊤ ℓ (λ _ _ → Except)
    runErr (Monad.return err-monad px) =
      return (inj₂ px)
    runErr (app (Monad.bind err-monad f) (partial mpx) σ) = do
      inj₂ px ×⟨ σ₂ ⟩ f ← mpx &⟨ _ ─✴ _ ∥ ⊎-comm σ ⟩ f
        where
          (inj₁ e ×⟨ σ₂ ⟩ f) → return (inj₁ e)
      case app f px (⊎-comm σ₂) of λ where
        (partial z) → z

  pattern error e = partial (inj₁ e)
  pattern ✓ x     = partial (inj₂ x)

module _ { M : Pt A ℓ } {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} where

  open ExceptTrans M {{ monad }}
  open Monads.Monad monad

  mapExc : ∀ {E₁ E₂ P} → (E₁ → E₂) → ∀[ Except E₁ P ⇒ Except E₂ P ]
  mapExc f (partial mc) = partial (mapM mc λ where (inj₁ e) → inj₁ (f e); (inj₂ px) → inj₂ px)

module ExceptMonad (Exc : Set ℓ) where
  open import Relation.Ternary.Separation.Monad.Identity
  open ExceptTrans Identity.Id {{ Identity.id-monad }} Exc public

data Error : Set ℓ where
  err : Error

module ErrorTrans
  (M : Pt A ℓ)
  {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} where

  open ExceptTrans M {{ monad }} Error public renaming (Except to Err)

module ErrorMonad where
  open import Relation.Ternary.Separation.Monad.Identity
  open ErrorTrans Identity.Id {{ Identity.id-monad }} public
