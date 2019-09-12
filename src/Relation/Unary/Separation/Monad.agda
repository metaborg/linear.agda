module Relation.Unary.Separation.Monad where

open import Level
open import Function using (_∘_; case_of_)
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality

module _ {a b} {A : Set a} {B : Set b} where
  _⇒[_]_ : ∀ {p q} (P : Pred A p) → (A → B) → (Q : Pred B q) → A → Set _
  P ⇒[ f ] Q = λ a → P a → Q (f a)

module _ {ℓ} {A : Set ℓ} {{sep : RawSep A}} {u} {{as : IsUnitalSep sep u}} where
  _─✴[_]_ : ∀ {b p q} {B : Set b} (P : A → Set p) → (A → B) → (Q : B → Set q) → A → Set _
  P ─✴[ j ] Q = P ─✴ (Q ∘ j)

module _
  {a b i} {A : Set a} {B : Set b} {I : Set i}
  {{sep : RawSep A}} {u} {{as : IsUnitalSep sep u}}
  {{ sep : RawSep B }}
  {j : A → B}
  {{ bs : IsUnitalSep sep (j ε) }} where

  {- strong, relative, indexed monads on predicates over SAs -}
  record Monad {ℓ} (M : (i j : I) → PT A B ℓ ℓ) : Set (a ⊔ b ⊔ suc ℓ ⊔ i) where
    field
      return : ∀ {P i₁}         → ∀[ P ⇒[ j ] M i₁ i₁ P ]
      bind   : ∀ {P i₁ i₂ i₃ Q} → ∀[ (P ─✴[ j ] M i₂ i₃ Q) ⇒[ j ] (M i₁ i₂ P ─✴ M i₁ i₃ Q) ]

    _=<<_ : ∀ {P Q i₁ i₂ i₃} → ∀[ P ⇒[ j ] M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]
    f =<< mp = app (bind (wand λ px σ → case ⊎-id⁻ˡ σ of λ where refl → f px)) mp ⊎-idˡ  

    _>>=_ : ∀ {Φ} {P Q i₁ i₂ i₃} → M i₁ i₂ P Φ → ∀[ P ⇒[ j ] M i₂ i₃ Q ] → M i₁ i₃ Q Φ
    mp >>= f = f =<< mp

  open Monad ⦃...⦄ public

module _
  {a b i} {A : Set a} {B : Set b} {I : Set i}
  {{sep : RawSep A}} {u} {{as : IsUnitalSep sep u}}
  {{ sep : RawSep B }}
  {j : A → B}
  {{ bs : IsUnitalSep sep (j ε) }} where

  data J (P : Pred A a) : Pred B (suc a) where
    inj : P Φ → J P (j Φ)

  -- having the internal bind is enough to get strength
  str : ∀ {P i₁ i₂} {M : (i j : I) → PT A B a a} {{ _ : Monad M }} (Q : Pred A a) →
        (M i₁ i₂ P ✴ J Q) Φ → M i₁ i₂ (P ✴ Q) Φ
  str _ (mp ×⟨ σ ⟩ inj qx) = app (bind (wand λ px σ' → return (px ×⟨ ⊎-comm σ' ⟩ qx))) mp (⊎-comm σ)

  syntax str Q mp qx = mp &[ Q ] qx
