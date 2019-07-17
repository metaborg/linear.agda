-- | An implementation of the Authoritative PCM
module Relation.Unary.Separation.Construct.Auth {A : Set} where

open import Level
open import Data.Product renaming (_,_ to _◐_)
open import Data.Maybe

import Data.Sum as Sum

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

record Auth : Set where
  constructor _◐_
  field
    auth : Maybe A -- the maybe indicates whether or not we own the whole
    frag : A

open Auth public

module _ ⦃ A-sep : RawUnitalSep A ⦄ where

  open RawUnitalSep A-sep
  open RawSep sep

  data ● {p} (P : Pred A p) : Pred Auth  p where
    authed   : ∀ {x} → P x → ● P (just x ◐ ε)

  data ○ {p} (P : Pred A p) : Pred Auth p where
    unauthed : ∀ {x} → P x → ○ P (nothing ◐ x)

  -- we directly define split on (A × A) instead
  -- of defininig it on the composite on (Maybe (Ex A) × A),
  -- to simplify defining functions/properties on it.
  data Split : Auth → Auth → Auth → Set where

    on-left : ∀ {x y y' z} →
               y ⊎ y' ≣ z →
               z ≤ x →
               Split (just x ◐ y) (nothing ◐ y') (just x ◐ z)

    on-right  : ∀ {x y y' z} →
               y ⊎ y' ≣ z →
               z ≤ x →
               Split (nothing ◐ y) (just x ◐ y') (just x ◐ z)

    neither  : ∀ {y y' z} →
               y ⊎ y' ≣ z →
               Split (nothing ◐ y) (nothing ◐ y') (nothing ◐ z)

  ◐-invₗ : ∀ {x z Φₗ Φᵣ Φ} → Split (x ◐ Φₗ) (nothing ◐ Φᵣ) (z ◐ Φ) → x ≡ z
  ◐-invₗ (on-left _ _) = refl
  ◐-invₗ (neither  _)  = refl

  ◐-invᵣ : ∀ {x z Φₗ Φᵣ Φ} → Split (nothing ◐ Φₗ) (x ◐ Φᵣ) (z ◐ Φ) → x ≡ z
  ◐-invᵣ (on-right _ _) = refl
  ◐-invᵣ (neither  _)   = refl

  frag-split : ∀ {Φₗ Φᵣ Φ} → Split Φₗ Φᵣ Φ → frag Φₗ ⊎ frag Φᵣ ≣ frag Φ
  frag-split (on-right x x₁)  = x
  frag-split (on-left x x₁) = x
  frag-split (neither x)     = x

  open RawSep
  auth-raw-sep : RawSep Auth
  _⊎_≣_ auth-raw-sep = Split

  auth-unital : RawUnitalSep Auth
  auth-unital = record { ε = nothing ◐ ε ; sep = auth-raw-sep }

module _ ⦃ A-sep : RawUnitalSep A ⦄ ⦃ _ : IsSep _≡_ (RawUnitalSep.sep A-sep) ⦄ where
  open IsSep ⦃...⦄

  func : ∀ {Φ₁ Φ₂ Φ Φ'} → Split Φ₁ Φ₂ Φ → Split Φ₁ Φ₂ Φ' → Φ ≡ Φ'
  func (on-right x le) (on-right y le') = cong (_ ◐_) (⊎-functional x y)
  func (on-left x le) (on-left y le')   = cong (_ ◐_) (⊎-functional x y)
  func (neither x) (neither y)          = cong (_ ◐_) (⊎-functional x y)

  cancelₗ : ∀ {Φ₁ Φ₁' Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₁' Φ₂ Φ → Φ₁ ≡ Φ₁'
  cancelₗ (on-right x le) (on-right y le') = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (on-left x le) (on-left y le')   = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (neither x) (neither y)          = cong (_ ◐_) (⊎-cancellative x y)

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (on-right x le) = on-left (⊎-comm x) le
  comm (on-left x le)  = on-right (⊎-comm x) le
  comm (neither x)     = neither (⊎-comm x)

  postulate assoc : ∀ {Φ₁ Φ₂ Ψ₁ Ψ₂ Ψ₃} →
                    Split Φ₁ Φ₂ Ψ₁ → Split Ψ₁ Ψ₂ Ψ₃ →
                    ∃ (λ ξ → Split Φ₂ Ψ₂ ξ × Split Φ₁ ξ Ψ₃)
  -- assoc (on-left y⊎y'≣z z≤w) (on-left z⊎z'≡z'' z''≤w) = {!!}
  -- assoc (on-right x x₁) (on-left x₂ x₃) = {!!}
  -- assoc (neither x) (on-right x₁ x₂) = {!!}
  -- assoc (neither x) (neither x₁) = {!!}

  instance auth-has-sep : IsSep _≡_ auth-raw-sep
  auth-has-sep = record
    { ⊎-functional = func
    ; ⊎-cancellative = cancelₗ
    ; ⊎-comm = comm
    ; ⊎-assoc = assoc
    }

--   auth-sep : Separation _ _
--   auth-sep = record
--     { set   = P.setoid Auth
--     ; isSep = auth-has-sep }

module _ ⦃ _ : IsUnitalSep {C = A} _≡_ ⦄  where
  open IsUnitalSep ⦃...⦄
  open RawUnitalSep unital 
  instance _ = unital
  instance _ = isSep
    
  instance auth-is-unital : IsUnitalSep {C = Auth} _≡_
  auth-has-unital = record
    { unital = record { ε = nothing ◐ ε ; sep = auth-raw-sep }
    ; isSep = auth-has-sep
    ; ⊎-identityˡ = λ where
                      {just x ◐ f} refl → on-right (⊎-identityˡ refl) {!!}
                      {nothing ◐ f} refl → neither (⊎-identityˡ refl)
    ; ⊎-identity⁻ˡ = {!!}
    ; ε-separateˡ = {!!} }

--   postulate ◐-identity⁻ˡ : ∀ {Φ} → ∀[ Split (ε ◐ ε) Φ ⇒ (Φ ≡_) ]
--   -- ◐-identity⁻ˡ (Authoritative.on-right x x₁) = {!subst₂ _≡_!}
--   -- ◐-identity⁻ˡ (Authoritative.on-left x x₁) = {!!}
--   -- ◐-identity⁻ˡ (Authoritative.neither x) = {!!}

-- -- module _ {A : Set} {_∙_}
-- --   {A-sep : RawUnitalSep A}
-- --   ⦃ _ : IsSep _≡_ (RawUnitalSep.sep A-sep) ⦄
-- --   ⦃ _ : IsConcattative (RawUnitalSep.sep A-sep) _∙_ ⦄ where

-- --   open IsSep ⦃...⦄
-- --   open Authoritative ⦃ A-sep ⦄

-- --   extend : 
