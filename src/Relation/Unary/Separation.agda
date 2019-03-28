{-# OPTIONS --safe --without-K #-}

-- A separation algebra.
-- Axiomatization based on
-- "A fresh look at Separation Algebras and Share Accounting" (Dockins et al)
module Relation.Unary.Separation where

open import Function
open import Level

open import Data.Unit using (tt)
open import Data.Product hiding (map)
open import Data.List.Relation.Ternary.Interleaving.Propositional hiding (map)
open import Data.List.Relation.Binary.Equality.Propositional

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
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
  record Conj {p q} (P : SPred p) (Q : ∀ {Φ} → P Φ → SPred q) Φ : Set (p ⊔ q ⊔ ℓ₁) where
    inductive
    constructor _×⟨_⟩_
    field
      {Φₗ Φᵣ} : A

      px  : P Φₗ
      sep : (Φₗ ⊎ Φᵣ) Φ
      qx  : Q px Φᵣ

  infixr 9 ∃[_]✴_
  ∃[_]✴_ = Conj

  infixr 9 _✴_
  _✴_ : ∀ {p q} → SPred p → SPred q → SPred (p ⊔ q ⊔ ℓ₁)
  P ✴ Q = ∃[ P ]✴ const Q

  -- mapping
  module _ {p q p' q'}
    {P : SPred p} {Q : SPred q} {P' : SPred p'} {Q' : SPred q'} where

    ⟨_⟨✴⟩_⟩ : (P ⊆ P') → (Q ⊆ Q') → P ✴ Q ⊆ P' ✴ Q'
    ⟨_⟨✴⟩_⟩ f g (px ×⟨ sep ⟩ qx) = (f px) ×⟨ sep ⟩ (g qx)

  -- separating implication or 'magic wand'
  infixr 8 _─✴_
  _─✴_ : ∀ {p q} (P : SPred p) (Q : SPred q) → SPred (p ⊔ q ⊔ ℓ₁)
  P ─✴ Q = λ Φᵢ → ∀ {Φₚ} → P Φₚ → ∀[ Φᵢ ⊎ Φₚ ⇒ Q ]

  _─✴′_ : ∀ {p q} (P : SPred p) (Q : SPred q) → SPred (p ⊔ q ⊔ ℓ₁)
  P ─✴′ Q = λ Φᵢ → ∀ {Φₚ Φ} → (P Φₚ × Φᵢ ⊎ Φₚ ≣ Φ) → Q Φ

  module _ {p q} {P : SPred p} {Q : SPred q} where
    apply : ∀[ (P ─✴ Q) ✴ P ⇒ Q ]
    apply (px ×⟨ sep ⟩ qx) =  px qx sep

  module _ {p q r} {P : SPred p} {Q : SPred q} {R : SPred r} where

    -- ✴-curry : ∀[ P ─✴ (Q ─✴ R) ] → ∀[ (P ✴ Q) ─✴ R ]
    -- ✴-curry f = wand (λ where
    --   (px ×⟨ sep₁ ⟩ qx) sep →
    --     let
    --       Φ , σ , σ' = ⊎-assoc (⊎-comm sep₁) {!⊎-comm sep!} 
    --       g = apply (f ×⟨ σ ⟩ px)
    --     in apply (g ×⟨ ⊎-comm σ' ⟩ qx))

    ✴-uncurry : ∀[ (P ✴ Q) ─✴ R ] → ∀[ P ─✴ (Q ─✴ R) ]
    ✴-uncurry f =
      λ px sep →
        λ qx sep' →
          let Φ , σ , σ' = ⊎-assoc sep sep'
          in  apply (f  ×⟨ σ' ⟩ (px ×⟨ σ ⟩ qx))

record Unital {c} (C : Set c) : Set c where
  field
    ε     : C

  ε[_] : ∀ {ℓ} → Pred C ℓ → Set ℓ
  ε[ P ] = P ε

record IsUnitalSep {c e} {C : Set c} (_≈_ : Rel C e)(sep : RawSep C) : Set (c ⊔ e) where
  field
    isSep  : IsSep _≈_ sep
    unital : Unital C

  open Unital unital
  open RawSep sep public

  field
    ⊎-identityˡ    : ∀ {Φ} → ∀[ (Φ ≡_) ⇒ (ε ⊎ Φ) ]
    ⊎-identity⁻ˡ   : ∀ {Φ} → ∀[ (ε ⊎ Φ) ⇒ (Φ ≡_) ]
    ε-separateˡ    : ∀ {Φᵣ} → ∀[ (_⊎ Φᵣ ≣ ε) ⇒ (_≡ ε) ]

  open IsSep isSep public

  ⊎-identityʳ : ∀ {Φ} → ∀[ (Φ ≡_) ⇒ (Φ ⊎ ε) ]
  ⊎-identityʳ = ⊎-comm ∘ ⊎-identityˡ

  ⊎-identity⁻ʳ : ∀ {Φ} → ∀[ (Φ ⊎ ε) ⇒ (Φ ≡_) ]
  ⊎-identity⁻ʳ = ⊎-identity⁻ˡ ∘ ⊎-comm

  ε-separateʳ : ∀ {Φₗ} → ∀[ (Φₗ ⊎_≣ ε) ⇒ (_≡ ε) ]
  ε-separateʳ = ε-separateˡ ∘ ⊎-comm

  {- Exactness -}
  module _ where

    Exactly : C → SPred c
    Exactly = flip _≡_

    _◆_ : C → C → SPred c
    Φₗ ◆ Φᵣ = Exactly Φₗ ✴ Exactly Φᵣ

  {- Emptyness -}
  module _ where

    Emp : SPred c
    Emp = Exactly ε

    ε⊎ε : ∀[ ε ⊎ ε ⇒ Emp ]
    ε⊎ε p with ⊎-identity⁻ˡ p
    ... | P.refl = P.refl

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

    frame_out_ : ∀ {ℓ} → C → SPred ℓ → SPred _
    frame j out P = (Exactly j) ✴ P

    _▣_ : ∀ {ℓ} → SPred ℓ → C → SPred _
    _▣_ = flip frame_out_

    pattern _⇑_ p sep = p IsSep.×⟨ sep ⟩ tt

  module ↑-Monadic {ℓ} {P : SPred ℓ} where

    return : ∀[ P ⇒ P ↑ ]
    return p = p ×⟨ ⊎-identityʳ P.refl ⟩ tt

    join : ∀[ (P ↑) ↑ ⇒ P ↑ ]
    join ((p ×⟨ σ₁ ⟩ tt) ×⟨ σ₂ ⟩ tt) = 
      let _ , σ₃ = ≤-trans (-, σ₁) (-, σ₂) in p ×⟨ σ₃ ⟩ tt

  module _ {ℓ₁ ℓ₂} {P : SPred ℓ₁} {Q : SPred ℓ₂} where

    map : ∀[ P ⇒ Q ] → ∀[ P ↑ ⇒ Q ↑ ]
    map f (px ⇑ sep) = f px ⇑ sep

  module _ {ℓ₁ ℓ₂} {P : SPred ℓ₁} {Q : SPred ℓ₂} where

    ↑-bind : ∀[ P ⇒ Q ↑ ] → ∀[ P ↑ ⇒ Q ↑ ]
    ↑-bind f px = ↑-Monadic.join (map f px)

  {- Projections out of separating conjunction using framing -}
  module _ where

    π₁ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ (P ✴ Q) ⇒ P ↑ ]
    π₁ (px ×⟨ sep ⟩ _) = px ⇑ sep

    π₂ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ (P ✴ Q) ⇒ Q ↑ ]
    π₂ (_ ×⟨ sep ⟩ qx) = qx ⇑ ⊎-comm sep


record IsConcattative {c} {C : Set c} (sep : RawSep C) (_∙_ : C → C → C) : Set c where
  open RawSep sep

  field
    ⊎-∙ : ∀ {Φₗ Φᵣ} → Φₗ ⊎ Φᵣ ≣ (Φₗ ∙ Φᵣ)

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

record MonoidalSep ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  field
    raw         : RawSep Carrier
    _∙_         : Carrier → Carrier → Carrier
    isUnitalSep : IsUnitalSep _≈_ raw
    isConcat    : IsConcattative raw _∙_

  open IsUnitalSep isUnitalSep public
  open IsConcattative isConcat public

  {- Disjoint extension -}
  module _ {ℓ₁ ℓ₂} where

    infixr 8 _─◆′_
    _─◆′_ : (P : SPred ℓ₁) (Q : ∀ {i} → P i → SPred ℓ₂)  → SPred _
    P ─◆′ Q = λ i → (p : P i) → ∃ (Q p)

    infixr 8 _─◆_
    _─◆_ : (P : SPred ℓ₁) (Q : SPred ℓ₂)  → SPred _
    P ─◆ Q = P ─◆′ (const Q)

    _─⟨_⟩_ : (P : SPred ℓ₁) → Carrier → (Q : SPred ℓ₂)  → SPred _
    P ─⟨ j ⟩ Q = P ⇒ Q ▣ j 

  {- Framing is functorial -}
  module _ where

    ▣-map : ∀ {j} {P : SPred ℓ₁} {Q : SPred ℓ₂} → ∀[ P ─◆ Q ] → ∀[ P ▣ j ─◆ Q ▣ j ]
    ▣-map f (px ×⟨ ◆ ⟩ qx) with f qx
    ... | ext , rx = -, px ×⟨ ⊎-∙ ⟩ rx
