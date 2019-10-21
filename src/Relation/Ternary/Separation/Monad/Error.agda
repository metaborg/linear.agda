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

module _ where
  record ExceptT (M : Pt A ℓ) (E : Set ℓ) (P : Pred A ℓ) (Φ : A) : Set ℓ where
    constructor partial
    field
      runErr : M ((λ _ → E) ∪ P) Φ

  open ExceptT public

  open import Relation.Ternary.Separation.Monad.Identity

  Except : ∀ E → Pt A ℓ
  Except E = ExceptT Identity.Id E

  pattern error e = partial (inj₁ e)
  pattern ✓ x     = partial (inj₂ x)

  data Err : Set ℓ where
    err : Err

  ErrorT : (M : Pt A ℓ) {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} → Pt A ℓ
  ErrorT M = ExceptT M Err

  open import Relation.Ternary.Separation.Monad.Identity

  Error : Pt A ℓ
  Error = ErrorT Identity.Id

module ExceptTrans
  (M : Pt A ℓ)
  {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} 
  (Exc : Set ℓ) where

  open Monads

  instance
    except-monad : Monad ⊤ ℓ (λ _ _ → ExceptT M Exc)
    runErr (Monad.return except-monad px) =
      return (inj₂ px)
    runErr (app (Monad.bind except-monad f) (partial mpx) σ) = do
      inj₂ px ×⟨ σ₂ ⟩ f ← mpx &⟨ _ ─✴ _ ∥ ⊎-comm σ ⟩ f
        where
          (inj₁ e ×⟨ σ₂ ⟩ f) → return (inj₁ e)
      case app f px (⊎-comm σ₂) of λ where
        (partial z) → z

  mapExc : ∀ {E₁ E₂ P} → (E₁ → E₂) → ∀[ ExceptT M E₁ P ⇒ ExceptT M E₂ P ]
  mapExc f (partial mc) = partial (mapM mc λ where (inj₁ e) → inj₁ (f e); (inj₂ px) → inj₂ px)

module ExceptMonad (Exc : Set ℓ) where
  open import Relation.Ternary.Separation.Monad.Identity
  open ExceptTrans Identity.Id {{ Identity.id-monad }} Exc public

module ErrorMonad where
  open import Relation.Ternary.Separation.Monad.Identity
  open ExceptTrans Identity.Id {{ Identity.id-monad }} Err public
