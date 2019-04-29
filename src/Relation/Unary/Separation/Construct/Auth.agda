-- | An implementation of the Authorative PCM
module Relation.Unary.Separation.Construct.Auth where

open import Level
open import Data.Product renaming (_,_ to _◐_)

import Data.Sum as Sum

open import Relation.Unary using (Pred)
open import Relation.Unary.Separation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P

module _ (A : Set) where
  data ▣ : Set where
    _◐_ : A → A → ▣

module Authoritative {A : Set} ⦃ A-sep : RawUnitalSep A ⦄ where
  open RawUnitalSep A-sep
  open RawSep sep

  data ● {p} (P : Pred A p) : Pred (▣ A) p where
    auth   : ∀ {x} → P x → ● P (x ◐ ε)

  data ○ {p} (P : Pred A p) : Pred (▣ A) p where
    unauth : ∀ {x} → P x → ○ P (ε ◐ x)

  data Split : ▣ A → ▣ A → ▣ A → Set where
    authₗ   : ∀ {x y y' z} →
              y ⊎ y' ≣ z →
              z ≤ x →
              Split (x ◐ y) (ε ◐ y') (x ◐ z)
    authᵣ   : ∀ {x y y' z} →
              y ⊎ y' ≣ z →
              z ≤ x →
              Split (ε ◐ y) (x ◐ y') (x ◐ z)
    unauth  : ∀ {y y' z} →
              y ⊎ y' ≣ z →
              Split (ε ◐ y) (ε ◐ y') (ε ◐ z)

  open RawSep
  auth-raw-sep : RawSep (▣ A)
  _⊎_≣_ auth-raw-sep = Split

  auth-unital : RawUnitalSep (▣ A)
  auth-unital = record { ε = ε ◐ ε ; sep = auth-raw-sep }

module _ {A : Set} {A-sep : RawUnitalSep A} ⦃ _ : IsSep _≡_ (RawUnitalSep.sep A-sep) ⦄ where
  open IsSep ⦃...⦄
  open Authoritative ⦃ A-sep ⦄

  -- meh :(
  func : ∀ {Φ₁ Φ₂ Φ Φ'} → Split Φ₁ Φ₂ Φ → Split Φ₁ Φ₂ Φ' → Φ ≡ Φ'
  func (authₗ x le) (authₗ y le') = cong (_ ◐_) (⊎-functional x y)
  func (authₗ x le) (authᵣ y le') = cong (_ ◐_) (⊎-functional x y)
  func (authₗ x le) (unauth y)    = cong (_ ◐_) (⊎-functional x y)
  func (authᵣ x le) (authₗ y le') = cong (_ ◐_) (⊎-functional x y)
  func (authᵣ x le) (authᵣ y le') = cong (_ ◐_) (⊎-functional x y)
  func (authᵣ x le) (unauth y)    = cong (_ ◐_) (⊎-functional x y)
  func (unauth x) (authₗ y le)    = cong (_ ◐_) (⊎-functional x y)
  func (unauth x) (authᵣ y le)    = cong (_ ◐_) (⊎-functional x y)
  func (unauth x) (unauth y)      = cong (_ ◐_) (⊎-functional x y)

  -- meh :(
  cancelₗ : ∀ {Φ₁ Φ₁' Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₁' Φ₂ Φ → Φ₁ ≡ Φ₁'
  cancelₗ (authₗ x le) (authₗ y le') = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (authₗ x le) (authᵣ y le') = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (authₗ x le) (unauth y)    = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (authᵣ x le) (authₗ y le') = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (authᵣ x le) (authᵣ y le') = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (authᵣ x le) (unauth y)    = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (unauth x) (authₗ y le)    = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (unauth x) (authᵣ y le)    = cong (_ ◐_) (⊎-cancellative x y)
  cancelₗ (unauth x) (unauth y)      = cong (_ ◐_) (⊎-cancellative x y)

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (authₗ x le) = authᵣ (⊎-comm x) le
  comm (authᵣ x le) = authₗ (⊎-comm x) le
  comm (unauth x)   = unauth (⊎-comm x)

  postulate auth-has-sep : IsSep _≡_ auth-raw-sep
  -- auth-has-sep = record
  --   { ⊎-functional = func
  --   ; ⊎-cancellative = cancelₗ
  --   ; ⊎-comm = comm
  --   ; ⊎-assoc = {!!}
  --   }

  auth-sep : Separation _ _
  auth-sep = record
    { set   = P.setoid (▣ A)
    ; isSep = auth-has-sep }
