{-# OPTIONS --without-K #-}

module Relation.Unary.Separation.Construct.Product where

open import Level
open import Data.Product

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
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

  instance ×-rawunitalsep : ⦃ _ : RawUnitalSep C₁ ⦄ ⦃ _ : RawUnitalSep C₂ ⦄ → RawUnitalSep (C₁ × C₂)
  ×-rawunitalsep ⦃ R₁ ⦄ ⦃ R₂ ⦄ =
    let open RawUnitalSep in
    record { ε = ε R₁ , ε R₂ ; sep = sep R₁ ×-⊎ sep R₂ }

module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {R₁ : RawSep C₁} {R₂ : RawSep C₂}
  ⦃ s₁ : IsSep R₁ ⦄ ⦃ s₂ : IsSep R₂ ⦄
  where

  instance postulate ×-isSep : IsSep (R₁ ×-⊎ R₂)

module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  ⦃ us₁ : RawUnitalSep C₁ ⦄ ⦃ us₂ : RawUnitalSep C₂ ⦄
  ⦃ u₁ : IsUnitalSep us₁ ⦄ ⦃ u₂ : IsUnitalSep us₂ ⦄
  where

  instance ×-isUnitalSep : IsUnitalSep ×-rawunitalsep
  ×-isUnitalSep = record
                      { isSep = ×-isSep
                      ; ⊎-idˡ = IsUnitalSep.⊎-idˡ u₁ , (IsUnitalSep.⊎-idˡ u₂)
                      ; ⊎-id⁻ˡ = λ where
                          (fst , snd) → cong₂ _,_ (IsUnitalSep.⊎-id⁻ˡ u₁ fst) (IsUnitalSep.⊎-id⁻ˡ u₂ snd)
                      }

module _
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  ⦃ s₁ : Separation ℓ₁ ℓ₂ ⦄ ⦃ s₂ : Separation ℓ₃ ℓ₄ ⦄
  where

  private
    module S₁ = Separation s₁
    module S₂ = Separation s₂

  ×-separation : Separation _ _
  ×-separation = record
    { set   = ×-setoid S₁.set S₂.set
    ; isSep = ×-isSep ⦃ Separation.isSep s₁ ⦄ ⦃ Separation.isSep s₂ ⦄ }

module _
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  ⦃ s₁ : UnitalSep ℓ₁ ℓ₂ ⦄ ⦃ s₂ : UnitalSep ℓ₃ ℓ₄ ⦄
  where

  private
    module S₁ = UnitalSep s₁
    module S₂ = UnitalSep s₂

  instance _×-ε-separation_ : UnitalSep _ _
  _×-ε-separation_ = record
    { set         = ×-setoid S₁.set S₂.set
    ; isUnitalSep = ×-isUnitalSep }

module _
  {ℓ₁ ℓ₂}
  {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  ⦃ sep₁ : RawSep C₁ ⦄ ⦃ sep₂ : RawSep C₂ ⦄
  ⦃ s₁ : IsConcattative sep₁ ⦄ ⦃ s₂ : IsConcattative sep₂ ⦄
  where

  private
    module S₁ = IsConcattative s₁
    module S₂ = IsConcattative s₂

  instance ×-concat : IsConcattative ×-rawsep
  ×-concat = record
    { _∙_ = (λ where (a , b) (c , d) → (a S₁.∙ c , b S₂.∙ d))
    ; ⊎-∙ = S₁.⊎-∙ , S₂.⊎-∙ }
