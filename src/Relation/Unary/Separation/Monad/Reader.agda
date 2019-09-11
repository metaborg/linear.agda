module Relation.Unary.Separation.Monad.Reader where

open import Level
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Env

open import Data.Product
open import Data.List

private
  variable
    ℓv : Level
    A  : Set ℓv
    Γ Γ₁ Γ₂ Γ₃ : List A

module Reader {ℓ}
  {T : Set ℓ}                              -- types
  {{m : MonoidalSep ℓ}}                    -- runtime resource
  (V : T → Pred (MonoidalSep.Carrier m) ℓ) -- values
  where
  
  open MonoidalSep m using (Carrier)

  variable
    P Q R : Pred Carrier ℓ

  record Reader (Γ₁ Γ₂ : List T) (P : Pred Carrier ℓ) (Φ : Carrier) : Set ℓ where
    constructor reader
    field
      runReader : (Allstar V Γ₁ ─✴ (Allstar V Γ₂ ✴ P)) Φ

  open Reader

  instance
    reader-monad : Monad Reader
    Monad.return reader-monad px = reader λ e s → e ×⟨ ⊎-comm s ⟩ px
    Monad.bind   reader-monad f mp σ₁ = reader λ env σ₂ →
      let
        _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
        env ×⟨ σ₅ ⟩ px = runReader mp env σ₄
        _ , σ₆ , σ₇ = ⊎-unassoc σ₃ (⊎-comm σ₅) 
      in runReader (f px σ₆) env σ₇

  frame : Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
  frame sep c = reader λ env σ →
    let
      E₁ ×⟨ σ₁ ⟩ E₂ = env-split sep env
      Φ , σ₂ , σ₃   = ⊎-unassoc σ σ₁
    in case runReader c E₁ σ₂ of λ where
      (nil ×⟨ σ₄ ⟩ px) → case ⊎-id⁻ˡ σ₄ of λ where
        refl → E₂ ×⟨ ⊎-comm σ₃ ⟩ px

  ask : ε[ Reader Γ ε (Allstar V Γ) ]
  ask = reader λ env σ → nil ×⟨ σ ⟩ env

  prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ∙ Γ₂) Emp ]
  prepend env₁ = reader λ env₂ s → env-∙ (env₁ ×⟨ s ⟩ env₂) ×⟨ ⊎-idʳ ⟩ empty

  append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ∙ Γ₁) Emp ]
  append env₁ = reader λ env₂ s → env-∙ (env₂ ×⟨ ⊎-comm s ⟩ env₁) ×⟨ ⊎-idʳ ⟩ empty
