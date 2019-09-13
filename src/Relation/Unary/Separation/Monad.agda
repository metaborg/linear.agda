module Relation.Unary.Separation.Monad where

open import Level
open import Function using (_∘_; case_of_)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Morphisms
open import Relation.Binary.PropositionalEquality

module Monads
  {a b} {A : Set a} {{r}} {u}
  {{as : IsUnitalSep {C = A} r u}} {{bs : Separation b}}
  (j : Morphism as bs)
  where

  open Separation bs using () renaming (Carrier to B)
  open Morphism j

  RawMonad : ∀ {i} (I : Set i) → (ℓ : Level) → Set _
  RawMonad I ℓ = (i j : I) → PT A B ℓ ℓ

  {- strong, relative, indexed monads on predicates over SAs -}
  record Monad {i} (I : Set i) ℓ (M : RawMonad I ℓ) : Set (a ⊔ b ⊔ suc ℓ ⊔ i) where
    field
      return : ∀ {P i₁}         → ∀[ P ⇒ⱼ M i₁ i₁ P ]
      bind   : ∀ {P i₁ i₂ i₃ Q} → ∀[ (P ─✴ⱼ M i₂ i₃ Q) ⇒ⱼ (M i₁ i₂ P ─✴ M i₁ i₃ Q) ]

    _=<<_ : ∀ {P Q i₁ i₂ i₃} → ∀[ P ⇒ⱼ M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]
    f =<< mp = app (bind (wand λ px σ → case ⊎-id⁻ˡ σ of λ where refl → f px)) mp ⊎-idˡ  

    _>>=_ : ∀ {Φ} {P Q i₁ i₂ i₃} → M i₁ i₂ P Φ → ∀[ P ⇒ⱼ M i₂ i₃ Q ] → M i₁ i₃ Q Φ
    mp >>= f = f =<< mp

  open Monad ⦃...⦄ public

  -- having the internal bind is enough to get strength
  str : ∀  {i} {I : Set i} {i₁ i₂} {P} {M} {{ _ : Monad I a M }} (Q : Pred A a) →
        (M i₁ i₂ P ✴ J Q) Φ → M i₁ i₂ (P ✴ Q) Φ
  str _ (mp ×⟨ σ ⟩ inj qx) =
    app
      (bind (wand λ px σ' → return (px ×⟨ ⊎-comm σ' ⟩ qx)))
      mp
      (⊎-comm σ)

  syntax str Q mp qx = mp &[ Q ] qx
