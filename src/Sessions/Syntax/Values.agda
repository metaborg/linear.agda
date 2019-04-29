module Sessions.Syntax.Values where

open import Prelude
open import Relation.Unary

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Data.List.Relation.Ternary.Interleaving

Chan : SType ∞ → Pred SCtx 0ℓ
Chan = Just

mutual
  data Closure : Type ∞ → Type ∞ → Pred SCtx 0ℓ where
    closure : ∀ {a} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Closure a b ]

  data Val : Type ∞ → Pred SCtx 0ℓ where
    tt   : ∀[ Emp           ⇒ Val unit       ]
    chan : ∀[ Chan α        ⇒ Val (chan α)   ]
    pair : ∀[ Val a ✴ Val b ⇒ Val (prod a b) ]
    clos : ∀[ Closure a b   ⇒ Val (a ⊸ b) ]

  Env : List (Type ∞) → Pred SCtx 0ℓ
  Env = Allstar Val

env-∙ : ∀[ Env Γ₁ ✴ Env Γ₂ ⇒ Env (Γ₁ ∙ Γ₂) ] 
env-∙ (nil refl ×⟨ s ⟩ env₂) rewrite ⊎-identity⁻ˡ s = env₂
env-∙ (cons (v ×⟨ s ⟩ env₁) ×⟨ s' ⟩ env₂) =
  let _ , eq₁ , eq₂ = ⊎-assoc s s' in
  cons (v ×⟨ eq₂ ⟩ (env-∙ (env₁ ×⟨ eq₁ ⟩ env₂)))

-- Environments can be split along context splittings
env-split : Γ₁ ⊎ Γ₂ ≣ Γ → ∀[ Env Γ ⇒ Env Γ₁ ✴ Env Γ₂ ] 
env-split [] (nil refl) = (nil refl) ×⟨ ⊎-identityˡ refl ⟩ (nil refl)
env-split (refl ∷ˡ s) (px :⟨ ◆ ⟩: sx) with env-split s sx
... | l ×⟨ ◆' ⟩ r with ⊎-assoc (⊎-comm ◆') (⊎-comm ◆)
... | (Δ , p , q) = cons (px ×⟨ ⊎-comm p ⟩ l) ×⟨ ⊎-comm q ⟩ r
env-split (refl ∷ʳ s) (px :⟨ ◆ ⟩: sx) with env-split s sx
... | l ×⟨ ◆' ⟩ r with ⊎-assoc ◆' (⊎-comm ◆)
... | (Δ , p , q) = l ×⟨ q ⟩ (cons (px ×⟨ ⊎-comm p ⟩ r))
