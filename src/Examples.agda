module Examples where

open import Prelude
open import Sessions.Syntax

module _ where
  open import Relation.Ternary.Separation.Construct.List Type

  lets : ∀[ Exp a ⇒ (a ∷_) ⊢ Exp b ─✴ Exp b ]
  app (lets e₁) e₂ σ = ap (lam _ e₂ ×⟨ ⊎-comm σ ⟩ e₁)

  -- The example from section 2.1 of the paper
  ex₁ : Exp unit ε
  ex₁ =
    letpair (mkchan (unit ! end) ×⟨ ⊎-idʳ ⟩ (
    lets (fork
      (letpair (recv (var refl) ×⟨ consˡ [] ⟩
        lam unit
          (letunit (letunit (var refl ×⟨ ⊎-∙ ⟩ var refl) ×⟨ consˡ (consʳ (consˡ [])) ⟩
          terminate (var refl)))))) $⟨ consʳ (consˡ []) ⟩
    (lets
      (send (unit ×⟨ ⊎-idˡ ⟩ (var refl))) $⟨ ⊎-comm ⊎-∙ ⟩
      letunit (var refl ×⟨ consʳ ⊎-∙ ⟩ terminate (var refl)))))


open import Sessions.Semantics.Expr
open import Sessions.Semantics.Process

comp = app (runReader nil) (eval 1000 ex₁) ⊎-idˡ
pool = start 1000 (main comp)

