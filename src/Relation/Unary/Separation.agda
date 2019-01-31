open import Data.List

module Relation.Unary.Separation where

open import Function
open import Level

open import Data.Unit using (tt)
open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Binary.Equality.Propositional

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)

open import Algebra
open import Algebra.FunctionProperties.Core

-- A separation algebra.
-- Axiomatized as in 
-- "A fresh look at Separation Algebras and Share Accounting" (Dockins et al)
record Separation ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  SPred : (ℓ : Level) → Set _
  SPred ℓ = Pred Carrier ℓ

  -- disjoint splitting
  field
    ε     : Carrier
    _⊎_≣_ : (Φ₁ Φ₂ : Carrier) → SPred ℓ₁

  -- we can see the three point relation as a predicate on the carrier
  _⊎_ = _⊎_≣_

  field
    ⊎-functional   : ∀ {Φ₁ Φ₂ Φ Φ'}   → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ⊎ Φ₂ ≣ Φ' → Φ ≈ Φ'
    ⊎-cancellative : ∀ {Φ₁ Φ₁' Φ₂}    → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₁' ⊎ Φ₂ ⇒ (λ _ → Φ₁ ≈ Φ₁') ]
    ⊎-comm         : ∀ {Φ₁ Φ₂}        → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₂ ⊎ Φ₁ ]
    ⊎-assoc        : ∀ {Φ₁ Φ₂ Φ₃ Φ Ψ} → Φ₁ ⊎ Φ₂ ≣ Φ → Φ ⊎ Φ₃ ≣ Ψ →
                                        ∃ λ Φ₄ → Φ₂ ⊎ Φ₃ ≣ Φ₄ × Φ₁ ⊎ Φ₄ ≣ Ψ
    ⊎-identityˡ    : ∀ {Φ}            → ∀[ (Φ ≈_) ⇒ (ε ⊎ Φ) ]

  ⊎-identityʳ : ∀ {Φ} → ∀[ (Φ ≈_) ⇒ (Φ ⊎ ε) ]
  ⊎-identityʳ = ⊎-comm ∘ ⊎-identityˡ

  variable
    Φ₁ Φ₂ Φ₃ Φ : Carrier

  -- separating conjunction
  module _ where
    infixr 9 _✴_
    record _✴_ {p q} (P : SPred p) (Q : SPred q) Φ : Set (p ⊔ q ⊔ ℓ₁ ⊔ ℓ₂) where
      constructor _×⟨_⟩_
      field
        {Φₗ Φᵣ} : Carrier

        px  : P Φₗ
        sep : (Φₗ ⊎ Φᵣ) Φ
        qx  : Q Φᵣ

  {- Emptyness -}
  module _ where

    data Emp : SPred 0ℓ where
      emp : Emp ε

  {- A free preorder -}
  module _ where
    -- embedding
    _≤_ : Carrier → Carrier → Set _
    Φ₁ ≤ Φ = ∃ λ Φ₂ → (Φ₁ ⊎ Φ₂) Φ

    ≤-reflexive : Φ₁ ≈ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive p = ε , ⊎-identityʳ p

    ≤-trans : Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁⊎τ₁=Φ₂) (τ₂ , Φ₂⊎τ₂=Φ₃) =
      let τ₃ , p , q = ⊎-assoc Φ₁⊎τ₁=Φ₂ Φ₂⊎τ₂=Φ₃ in τ₃ , q

    ≤-isPreorder : IsPreorder _≈_ _≤_
    ≤-isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

  {- Framing -}
  module _ where

    infixl 1000 _↑
    _↑ : ∀ {ℓ} → SPred ℓ → SPred _
    P ↑ = P ✴ U

    module ↑-Monadic {ℓ} {P : SPred ℓ} where

      return : ∀[ P ⇒ P ↑ ]
      return p = p ×⟨ ⊎-identityʳ refl ⟩ tt

      join : ∀[ (P ↑) ↑ ⇒ P ↑ ]
      join ((p ×⟨ σ₁ ⟩ tt) ×⟨ σ₂ ⟩ tt) = 
        let _ , σ₃ = ≤-trans (-, σ₁) (-, σ₂) in p ×⟨ σ₃ ⟩ tt

  -- {- Pointer to a single element -}
  -- module _ {ℓ} (P : APred ℓ) where

  --   Any : SPred _
  --   Any = (Only P) ↑

  --   pattern here  p    = single p ×⟨ consˡ _ ⟩ _
  --   pattern there sp r = single _ ×⟨ consʳ sp ⟩ r

  -- In : A → SPred _
  -- In a = Any (_≡_ a)

  -- {- Big seperating conjunction over an SPred -}
  -- module _ {ℓ} (P : SPred ℓ) where

  --   data Allstar : SPred (a ⊔ ℓ) where
  --     emp  : ∀[ Emp ⇒ Allstar ]
  --     star : ∀[ P ✴ Allstar ⇒ Allstar ]

  --   -- find : ∀ {q a} {Q : APred q} → ∀[ In a ⇒ Allstar ⇒ P ↑ ]
  --   -- find (here _)    (emp ())
  --   -- find (here _)    (star (p ×⟨ σ ⟩ q)) = {!p!}
  --   -- find (there sp r) (emp ())
  --   -- find (there sp r) (star (p ×⟨ σ ⟩ q)) = {!find ? q!}
