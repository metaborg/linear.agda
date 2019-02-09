-- A separation algebra.
-- Axiomatization based on
-- "A fresh look at Separation Algebras and Share Accounting" (Dockins et al)
module Relation.Unary.Separation where

open import Function
open import Level

open import Data.Unit using (tt)
open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Binary.Equality.Propositional

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Algebra
open import Algebra.FunctionProperties.Core

record RawSep {a} (Carrier : Set a) : Set (suc a) where

  SPred : (ℓ : Level) → Set _
  SPred ℓ = Pred Carrier ℓ

  field
    _⊎_≣_ : (Φ₁ Φ₂ : Carrier) → SPred a

  -- we can see the three point relation as a predicate on the carrier
  _⊎_ = _⊎_≣_

record IsSep {ℓ₁ ℓ₂} {A} (_≈_ : (l r : A) → Set ℓ₂) (s : RawSep {ℓ₁} A) : Set (ℓ₁ ⊔ ℓ₂) where
  open RawSep s

  field
    ⊎-functional   : ∀ {Φ₁ Φ₂ Φ Φ'}   → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ⊎ Φ₂ ≣ Φ' → Φ ≈ Φ'
    ⊎-cancellative : ∀ {Φ₁ Φ₁' Φ₂}    → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₁' ⊎ Φ₂ ⇒ (λ _ → Φ₁ ≈ Φ₁') ]
    ⊎-comm         : ∀ {Φ₁ Φ₂}        → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₂ ⊎ Φ₁ ]
    ⊎-assoc        : ∀ {Φ₁ Φ₂ Φ₃ Φ Ψ} → Φ₁ ⊎ Φ₂ ≣ Φ → Φ ⊎ Φ₃ ≣ Ψ →
                                        ∃ λ Φ₄ → Φ₂ ⊎ Φ₃ ≣ Φ₄ × Φ₁ ⊎ Φ₄ ≣ Ψ

  variable
    Φ₁ Φ₂ Φ₃ Φ : A

  -- separating conjunction
  infixr 9 _✴_
  record _✴_ {p q} (P : SPred p) (Q : SPred q) Φ : Set (p ⊔ q ⊔ ℓ₁) where
    inductive
    constructor _×⟨_⟩_
    field
      {Φₗ Φᵣ} : A

      px  : P Φₗ
      sep : (Φₗ ⊎ Φᵣ) Φ
      qx  : Q Φᵣ

record IsUnitalSep {c e} {C : Set c} (_≈_ : Rel C e)(sep : RawSep C) : Set (c ⊔ e) where
  field
    isSep : IsSep _≈_ sep
    ε     : C

  open RawSep sep public

  field
    ⊎-identityˡ    : ∀ {Φ}            → ∀[ (Φ ≡_) ⇒ (ε ⊎ Φ) ]

  open IsSep isSep public

  ⊎-identityʳ : ∀ {Φ} → ∀[ (Φ ≡_) ⇒ (Φ ⊎ ε) ]
  ⊎-identityʳ = ⊎-comm ∘ ⊎-identityˡ

  {- Exactness -}
  module _ where

    Exactly : C → SPred c
    Exactly = flip _≡_

  {- Emptyness -}
  module _ where

    Emp : SPred c
    Emp = Exactly ε

  {- Big seperating conjunction over an SPred -}
  module _ where

    data Allstar {ℓ} (P : SPred ℓ) : SPred (ℓ ⊔ c) where
      emp  : ∀[ Emp ⇒ Allstar P ]
      star : ∀[ P ✴ Allstar P ⇒ Allstar P ]

  {- A free preorder -}
  module _ where

    _≤_ : Rel C _
    Φ₁ ≤ Φ = ∃ λ Φ₂ → (Φ₁ ⊎ Φ₂) Φ

    ≤-reflexive : Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive p = ε , ⊎-identityʳ p

    ≤-trans : Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁⊎τ₁=Φ₂) (τ₂ , Φ₂⊎τ₂=Φ₃) =
      let τ₃ , p , q = ⊎-assoc Φ₁⊎τ₁=Φ₂ Φ₂⊎τ₂=Φ₃ in τ₃ , q

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

  {- Framing -}
  module _ where

    infixl 1000 _↑
    _↑ : ∀ {ℓ} → SPred ℓ → SPred _
    P ↑ = P ✴ U

    pattern _⇑_ p sep = p IsSep.×⟨ sep ⟩ tt

    module ↑-Monadic {ℓ} {P : SPred ℓ} where

      return : ∀[ P ⇒ P ↑ ]
      return p = p ×⟨ ⊎-identityʳ P.refl ⟩ tt

      join : ∀[ (P ↑) ↑ ⇒ P ↑ ]
      join ((p ×⟨ σ₁ ⟩ tt) ×⟨ σ₂ ⟩ tt) = 
        let _ , σ₃ = ≤-trans (-, σ₁) (-, σ₂) in p ×⟨ σ₃ ⟩ tt

    π₁ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ (P ✴ Q) ⇒ P ↑ ]
    π₁ (px ×⟨ sep ⟩ _) = px ⇑ sep

    π₂ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ (P ✴ Q) ⇒ Q ↑ ]
    π₂ (_ ×⟨ sep ⟩ qx) = qx ⇑ ⊎-comm sep

record Separation ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  field
    raw          : RawSep Carrier
    isSep : IsSep _≈_ raw

  open RawSep raw public
  open IsSep isSep public

record UnitalSep ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  field
    raw         : RawSep Carrier
    isUnitalSep : IsUnitalSep _≈_ raw

  open IsUnitalSep isUnitalSep public
