{-# OPTIONS --without-K #-}

module Relation.Unary.Separation.Construct.Product where

open import Level
open import Data.Product

open import Relation.Unary.Separation
open import Relation.Binary
open import Data.Product.Relation.Binary.Pointwise.NonDependent

module _ {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂} where

  _×-⊎_ : RawSep C₁ → RawSep C₂ → RawSep (C₁ × C₂)
  R₁ ×-⊎ R₂ =
    let
      module R₁ = RawSep R₁
      module R₂ = RawSep R₂
    in record
    { _⊎_≣_ = λ Φ₁ Φ₂ Φ →
        (proj₁ Φ₁) R₁.⊎ (proj₁ Φ₂) ≣ proj₁ Φ
      × (proj₂ Φ₁) R₂.⊎ (proj₂ Φ₂) ≣ proj₂ Φ }

  instance ×-rawsep : ⦃ _ : RawSep C₁ ⦄ ⦃ _ : RawSep C₂ ⦄ → RawSep (C₁ × C₂)
  ×-rawsep ⦃ R₁ ⦄ ⦃ R₂ ⦄ = R₁ ×-⊎ R₂

  postulate instance ×-rawunitalsep : ⦃ _ : RawUnitalSep C₁ ⦄ ⦃ _ : RawUnitalSep C₂ ⦄ → RawUnitalSep (C₁ × C₂)

module _
  {ℓ₁ ℓ₂ e₁ e₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {_≈₁_ : Rel C₁ e₁} {_≈₂_ : Rel C₂ e₂}
  {R₁ : RawSep C₁} {R₂ : RawSep C₂}
  (s₁ : IsSep _≈₁_ R₁) (s₂ : IsSep _≈₂_ R₂)
  where

  postulate _×-isSep_ : IsSep (Pointwise _≈₁_ _≈₂_) (R₁ ×-⊎ R₂)

module _
  {ℓ₁ ℓ₂ e₁ e₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {_≈₁_ : Rel C₁ e₁} {_≈₂_ : Rel C₂ e₂}
  (s₁ : IsUnitalSep _≈₁_) (s₂ : IsUnitalSep _≈₂_)
  where

  postulate _×-isUnitalSep_ : IsUnitalSep (Pointwise _≈₁_ _≈₂_)

module _
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  (s₁ : Separation ℓ₁ ℓ₂) (s₂ : Separation ℓ₃ ℓ₄)
  where

  private
    module S₁ = Separation s₁
    module S₂ = Separation s₂

  _×-separation_ : Separation _ _
  _×-separation_ = record
    { set   = ×-setoid S₁.set S₂.set
    ; isSep = S₁.isSep ×-isSep S₂.isSep }

module _
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  (s₁ : UnitalSep ℓ₁ ℓ₂) (s₂ : UnitalSep ℓ₃ ℓ₄)
  where

  private
    module S₁ = UnitalSep s₁
    module S₂ = UnitalSep s₂

  _×-ε-separation_ : UnitalSep _ _
  _×-ε-separation_ = record
    { set         = ×-setoid S₁.set S₂.set
    ; isUnitalSep = S₁.isUnitalSep ×-isUnitalSep S₂.isUnitalSep }
