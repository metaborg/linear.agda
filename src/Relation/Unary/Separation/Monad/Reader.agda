{-# OPTIONS --allow-unsolved-metas #-}
module Relation.Unary.Separation.Monad.Reader where

open import Level
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Env

open import Data.Product
open import Data.List
open import Data.Unit

private
  variable
    ℓv : Level
    A  : Set ℓv
    Γ Γ₁ Γ₂ Γ₃ : List A

{- Something not unlike a indexed relative monad transformer in a bicartesian closed category -}
module Reader {ℓ}
  {T : Set ℓ}           -- types
  {{m : MonoidalSep ℓ}} -- runtime resource
  {{s : Separation ℓ}}
  (j : Morphism (MonoidalSep.isUnitalSep m) s)
  (V : T → Pred (MonoidalSep.Carrier m) ℓ) -- values
  (M : PT (MonoidalSep.Carrier m) (Separation.Carrier s) ℓ ℓ)
  where

  open Monads j
  
  module _ {{_ : Monad ⊤ ℓ (λ _ _ → M) }} where
    open MonoidalSep m using () renaming (Carrier to C)
    open Separation s using () renaming (Carrier to B)
    open Morphism j hiding (j)

    variable
      P Q R : Pred C ℓ

    Reader : ∀ (Γ₁ Γ₂ : List T) (P : Pred C ℓ) → Pred B ℓ
    Reader Γ₁ Γ₂ P = J (Allstar V Γ₁) ─✴ M (P ✴ Allstar V Γ₂)

    instance
      reader-monad : Monad (List T) _ Reader
      app (Monad.return reader-monad px) e s = str _ (return px ×⟨ s ⟩ e)
      app (app (Monad.bind reader-monad f) mp σ₁) env σ₂ =
        let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in
        app (bind (wand λ where
          (px ×⟨ σ₅ ⟩ env') σ₆ →
            let _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₅) (⊎-comm σ₆)
            in app (app f px (⊎-comm τ₂)) (inj env') (j-map (⊎-comm τ₁)))) (app mp env σ₄) σ₃

    frame : Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
    app (frame sep c) (inj env) σ = do
      let E₁ ×⟨ σ₁ ⟩ E₂ = env-split sep env
      let Φ , σ₂ , σ₃   = ⊎-unassoc σ (j-map σ₁)
      (v ×⟨ σ₄ ⟩ nil) ×⟨ σ₅ ⟩ E₃ ← str (Allstar _ _) (app c (inj E₁) σ₂ ×⟨ σ₃ ⟩ inj E₂)
      case ⊎-id⁻ʳ σ₄ of λ where
        refl → return (v ×⟨ σ₅ ⟩ E₃)

    ask : ε[ Reader Γ ε (Allstar V Γ) ]
    app ask (inj env) σ with ⊎-id⁻ˡ σ
    ... | refl = return (env ×⟨ ⊎-idʳ ⟩ nil)

    prepend : ∀[ Allstar V Γ₁ ⇒ⱼ Reader Γ₂ (Γ₁ ∙ Γ₂) Emp ]
    app (prepend env₁) (inj env₂) s with j-⊎ s
    ... | _ , refl = return (empty ×⟨ ⊎-idˡ ⟩ (env-∙ (env₁ ×⟨ j-map⁻ s ⟩ env₂)))

    append : ∀[ Allstar V Γ₁ ⇒ⱼ Reader Γ₂ (Γ₂ ∙ Γ₁) Emp ]
    app (append env₁) (inj env₂) s with j-⊎ s
    ... | _ , refl = return (empty ×⟨ ⊎-idˡ ⟩ (env-∙ (✴-swap (env₁ ×⟨ j-map⁻ s ⟩ env₂))))

    liftM : ∀[ M P ⇒ Reader Γ Γ P ]
    app (liftM mp) env σ = do
      str _ (mp ×⟨ σ ⟩ env)
