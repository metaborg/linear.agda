module Relation.Unary.Separation.Construct.Product where

open import Data.Product

open import Relation.Unary.Separation
open import Relation.Binary
open import Data.Product.Relation.Binary.Pointwise.NonDependent

module _ {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂} where

  _×-⊎_ : RawSeparation C₁ → RawSeparation C₂ → RawSeparation (C₁ × C₂)
  R₁ ×-⊎ R₂ =
    let
      module R₁ = RawSeparation R₁
      module R₂ = RawSeparation R₂
    in record
    { ε     = R₁.ε , R₂.ε
    ; _⊎_≣_ = λ Φ₁ Φ₂ Φ →
        (proj₁ Φ₁) R₁.⊎ (proj₁ Φ₂) ≣ proj₁ Φ
      × (proj₂ Φ₁) R₂.⊎ (proj₂ Φ₂) ≣ proj₂ Φ }

module _
  {ℓ₁ ℓ₂ e₁ e₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {_≈₁_ : Rel C₁ e₁} {_≈₂_ : Rel C₂ e₂}
  {R₁ : RawSeparation C₁} {R₂ : RawSeparation C₂}
  (s₁ : IsSeparation _≈₁_ R₁) (s₂ : IsSeparation _≈₂_ R₂)
  where

  postulate _×-isSeparation_ : IsSeparation (Pointwise _≈₁_ _≈₂_) (R₁ ×-⊎ R₂)

module _
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  (s₁ : Separation ℓ₁ ℓ₂) (s₂ : Separation ℓ₃ ℓ₄)
  where

  private
    module S₁ = Separation s₁
    module S₂ = Separation s₂

  _×-separation_ : Separation _ _
  _×-separation_ = record
    { set = ×-setoid S₁.set S₂.set
    ; isSeparation = S₁.isSeparation ×-isSeparation S₂.isSeparation }
