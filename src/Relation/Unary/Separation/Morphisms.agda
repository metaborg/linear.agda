module Relation.Unary.Separation.Morphisms where

open import Level
open import Function
open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function using (_∘_)

record Morphism {a b} (A : Set a) (B : Set b)
  {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}}
  {{rb : RawSep B}} : Set (a ⊔ suc b) where

  field
    j      : A → B
    j-map  : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ⊎ Φ₂ ≣ Φ → j Φ₁ ⊎ j Φ₂ ≣ j Φ
    j-⊎    : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ⊎ j Φ₂ ≣ Φ → ∃ λ Φ' → Φ ≡ j Φ'
    j-map⁻ : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ⊎ j Φ₂ ≣ j Φ → Φ₁ ⊎ Φ₂ ≣ Φ

  instance _ = s₁

  {- Such a morphism on SAs induces a functor on SA-predicates -}
  module _ where

    data J {p} (P : Pred A p) : Pred B (a ⊔ p) where
      inj : ∀ {Φ} → P Φ → J P (j Φ)

    jstar : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J (P ✴ Q) ⇒ J P ✴ J Q ]
    jstar (inj (p ×⟨ σ ⟩ q)) = inj p ×⟨ j-map σ ⟩ inj q

    jstar⁻ : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J P ✴ J Q ⇒ J (P ✴ Q) ]
    jstar⁻ (inj px ×⟨ σ ⟩ inj qx) with j-⊎ σ
    ... | _ , refl = inj (px ×⟨ j-map⁻ σ ⟩ qx)

  {- relative morphisms -}
  infixr 8 _⇒ⱼ_
  _⇒ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _ 
  P ⇒ⱼ Q = P ⇒ (Q ∘ j)

  {- relative exponents -}
  infixr 8 _─✴ⱼ_
  _─✴ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _ 
  P ─✴ⱼ Q = P ─✴ (Q ∘ j)

  wanditⱼ : ∀ {p q} {P : Pred A p} {Q : Pred B q} → ∀[ P ⇒ⱼ Q ] → (P ─✴ⱼ Q) u
  app (wanditⱼ f) px σ rewrite ⊎-id⁻ˡ σ = f px

module _ {a} {A : Set a} {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}} where

  instance id-morph : Morphism A A
  id-morph = record 
    { j = id
    ; j-map = id 
    ; j-⊎ = λ x → -, refl 
    ; j-map⁻ = id }
