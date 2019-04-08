module Sessions.Semantics where

open import Size
open import Level
open import Function
open import Data.Product
open import Data.List
open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary using (Rel; IsPreorder; Preorder)
open import Relation.Binary.PropositionalEquality

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr
open import Sessions.Syntax.Runtime

open UnitalSep ⦃...⦄ hiding (refl)

_⊑_ : Rel LCtx 0ℓ
_⊑_ = _≤_

postulate
  ⊑-isPre : IsPreorder _≡_ _⊑_

⊑-pre : Preorder _ _ _
⊑-pre = record
  { isPreorder = ⊑-isPre }

open import Relation.Unary.Closure.Preorder ⊑-pre

postulate
  Buffers : Pred SCtx 0ℓ

M : SCtx → Pt LCtx 0ℓ
M Φ P Γ = Buffers Φ → ((flip Env Φ) ─✴ (λ Γ' → P Γ' × Buffers Φ)) Γ

return : ∀ {P} → ∀[ P ⇒ M ε P ]
return {P} px μ E ◆ = {!E!} -- _ , ≤-reflexive refl , px , snd

_>>=_ : ∀ {Γ₁ Γ₂ P Q} → ∀[ M Γ₁ P ⇒ □ (P ⇒ M Γ₂ Q) ⇒ M (Γ₁ ++ Γ₂) Q ]
m >>= f = {!!}

-- ask : ∀ {Γ} → ∀[ M Γ (Env Γ) ]
-- ask (E , β) = -, ≤-reflexive refl , E , β

-- eval : ∀ {Γ a} → Exp a Γ → ∀[ M Γ (Val a) ]
-- eval (var x)       = λ x₁ → {!!}
-- eval (unit refl)   = return (tt {!!}) -- return (tt refl)
-- eval (λₗ a x)      = do
--   E ← ask
--   {!!}
--   -- return (clos {!!} {!!})
-- eval (_·_ x)       = {!!}
-- eval (pair x)      = {!!}
-- eval (letpair x)   = {!!}
-- eval (send x)      = {!!}
-- eval (recv e)      = {!!}
-- eval (link x)      = {!!}
-- eval (terminate e) = {!!}
