open import Relation.Unary.Separation

module Relation.Unary.Separation.Env 
  {t v ℓ₁}
  {T : Set t}
  {C : Set ℓ₁} {{rc : RawSep C}} {u} {{sc : IsUnitalSep rc u}} {{cc : IsConcattative rc}}
  {V : T → C → Set v} where

open import Data.Product
open import Data.List

open import Relation.Unary
open import Relation.Unary.Separation.Construct.List
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
open import Relation.Binary.PropositionalEquality as P hiding ([_])

env-∙ : ∀ {Γ₁ Γ₂ : List T} → ∀[ Allstar V Γ₁ ✴ Allstar V Γ₂ ⇒ Allstar V (Γ₁ ∙ Γ₂) ] 
env-∙ (nil ×⟨ s ⟩ env₂) rewrite ⊎-id⁻ˡ s = env₂
env-∙ (cons (v ×⟨ s ⟩ env₁) ×⟨ s' ⟩ env₂) =
  let _ , eq₁ , eq₂ = ⊎-assoc s s' in
  cons (v ×⟨ eq₁ ⟩ (env-∙ (env₁ ×⟨ eq₂ ⟩ env₂)))

-- Allstarironments can be split along context splittings
env-split : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊎ Γ₂ ≣ Γ → ∀[ Allstar V Γ ⇒ Allstar V Γ₁ ✴ Allstar V Γ₂ ] 
env-split = repartition
