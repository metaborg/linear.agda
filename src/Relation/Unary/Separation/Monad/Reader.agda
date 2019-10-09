module Relation.Unary.Separation.Monad.Reader where

open import Level
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Allstar

open import Data.Product
open import Data.List hiding (concat)
open import Data.Unit

private
  variable
    ℓv : Level
    A  : Set ℓv
    Γ Γ₁ Γ₂ Γ₃ : List A

{- Something not unlike a indexed relative monad transformer in a bicartesian closed category -}
module Reader {ℓ}
  -- types
  {T : Set ℓ}
  -- runtime resource
  {C : Set ℓ} {{rc : RawSep C}} {u} {{sc : IsUnitalSep rc u}} {{cc : IsConcattative rc}}
  --
  {B : Set ℓ} {{rb : RawSep B}}
  (j : Morphism C B) {{sb : IsUnitalSep rb (Morphism.j j u)}}
  (V : T → Pred C ℓ) -- values
  (M : PT C B ℓ ℓ)
  where

  open Monads {{j = j}} using (Monad; str)
  
  module _ {{monad : Monad ⊤ ℓ (λ _ _ → M) }} where
    open Morphism j hiding (j) public
    open Monad monad

    variable
      P Q R : Pred C ℓ

    Reader : ∀ (Γ₁ Γ₂ : List T) (P : Pred C ℓ) → Pred B ℓ
    Reader Γ₁ Γ₂ P = J (Allstar V Γ₁) ─✴ M (P ✴ Allstar V Γ₂)

    instance
      reader-monad : Monad (List T) _ Reader
      app (Monad.return reader-monad px) (inj e) s = app (str e) (return px) (⊎-comm s)
      app (app (Monad.bind reader-monad f) mp σ₁) env σ₂ =
        let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in
        app (bind (wand λ where
          (px ×⟨ σ₅ ⟩ env') σ₆ →
            let _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₅) (⊎-comm σ₆)
            in app (app f px (⊎-comm τ₂)) (inj env') (j-map (⊎-comm τ₁)))) (app mp env σ₄) σ₃

    open import Relation.Unary.Separation.Construct.List T

    frame : Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
    app (frame sep c) (inj env) σ = do
      let E₁ ×⟨ σ₁ ⟩ E₂ = repartition sep env
      let Φ , σ₂ , σ₃   = ⊎-unassoc σ (j-map σ₁)
      (v ×⟨ σ₄ ⟩ nil) ×⟨ σ₅ ⟩ E₃ ← app (str {Q = Allstar _ _} E₂) (app c (inj E₁) σ₂) (⊎-comm σ₃)
      case ⊎-id⁻ʳ σ₄ of λ where
        refl → return (v ×⟨ σ₅ ⟩ E₃)

    ask : ε[ Reader Γ ε (Allstar V Γ) ]
    app ask (inj env) σ with ⊎-id⁻ˡ σ
    ... | refl = return (env ×⟨ ⊎-idʳ ⟩ nil)

    prepend : ∀[ Allstar V Γ₁ ⇒ⱼ Reader Γ₂ (Γ₁ ∙ Γ₂) Emp ]
    app (prepend env₁) (inj env₂) s with j-⊎ s
    ... | _ , refl = return (empty ×⟨ ⊎-idˡ ⟩ (concat (env₁ ×⟨ j-map⁻ s ⟩ env₂)))

    append : ∀[ Allstar V Γ₁ ⇒ⱼ Reader Γ₂ (Γ₂ ∙ Γ₁) Emp ]
    app (append env₁) (inj env₂) s with j-⊎ s
    ... | _ , refl = return (empty ×⟨ ⊎-idˡ ⟩ (concat (✴-swap (env₁ ×⟨ j-map⁻ s ⟩ env₂))))

    liftM : ∀[ M P ⇒ Reader Γ Γ P ]
    app (liftM mp) (inj env) σ = do
      app (str env) mp (⊎-comm σ)

    runReader : ∀[ Allstar V Γ ⇒ⱼ Reader Γ ε P ─✴ M P ]
    app (runReader env) mp σ = do
      px ×⟨ σ ⟩ nil ← app mp (inj env) (⊎-comm σ)
      case ⊎-id⁻ʳ σ of λ where
        refl → return px 
