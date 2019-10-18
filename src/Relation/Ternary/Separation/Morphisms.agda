module Relation.Ternary.Separation.Morphisms where

open import Level
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Separation
open import Data.Product
open import Function using (_∘_)

record Morphism {a b} (A : Set a) (B : Set b)
  {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}}
  {{rb : RawSep B}} : Set (a ⊔ suc b) where

  field
    j    : A → B

    -- j "commutes" with _⊎_
    j-⊎  : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ⊎ Φ₂ ≣ Φ → j Φ₁ ⊎ j Φ₂ ≣ j Φ
    j-⊎⁻ : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ⊎ j Φ₂ ≣ Φ → ∃ λ Φ' → Φ ≡ j Φ' × Φ₁ ⊎ Φ₂ ≣ Φ'

  instance _ = s₁

  infixr 8 _⇒ⱼ_
  _⇒ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _ 
  P ⇒ⱼ Q = P ⇒ (Q ∘ j)

  infixr 8 _─✴ⱼ_
  _─✴ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred B _ 
  P ─✴ⱼ Q = P ─✴[ j ] Q

  {- Such a morphism on SAs induces a functor on SA-predicates -}
  module _ where

    data J {p} (P : Pred A p) : Pred B (a ⊔ p) where
      inj : ∀ {Φ} → P Φ → J P (j Φ)

    jstar : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J (P ✴ Q) ⇒ J P ✴ J Q ]
    jstar (inj (p ×⟨ σ ⟩ q)) = inj p ×⟨ j-⊎ σ ⟩ inj q

    jmap : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ (P ─✴ Q) ⇒ⱼ (J P ─✴ J Q) ]
    app (jmap f) (inj px) σ with j-⊎⁻ σ
    ... | _ , refl , σ' = inj (app f px σ')

  wanditⱼ : ∀ {p q} {P : Pred A p} {Q : Pred B q} → ∀[ P ⇒ⱼ Q ] → (P ─✴ⱼ Q) (j u)
  app (wanditⱼ f) px σ with j-⊎⁻ σ
  ... | _ , refl , σ' with ⊎-id⁻ˡ σ'
  ... | refl = f px

{- identity morphism -}
module _ {a} {A : Set a} {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}} where

  instance id-morph : Morphism A A
  id-morph = record 
    { j   = id
    ; j-⊎ = id 
    ; j-⊎⁻ = λ x → -, refl , x
    }
