-- | An implementation of the Marketoritative PCM
module Relation.Unary.Separation.Construct.Market where

open import Level hiding (Lift)
open import Data.Product
open import Data.Maybe

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

module _ {ℓ} (A : Set ℓ) where

  data Market : Set ℓ where
    offer  : (l : A) → Market
    demand : (r : A) → Market

module _ {ℓ} {A : Set ℓ} {{ sep : RawSep A }} {{ _ : IsSep sep }} where

  data Split : Market A → Market A → Market A → Set ℓ where

    offerₗ : {r l₁ l₂ : A} (σ : l₂ ⊎ r ≣ l₁) → Split (offer l₁) (demand r) (offer l₂)
    offerᵣ : {r l₁ l₂ : A} (σ : r ⊎ l₂ ≣ l₁) → Split (demand r) (offer l₁) (offer l₂)
    demand : {r₁ r₂ r : A} (σ : r₁ ⊎ r₂ ≣ r) → Split (demand r₁) (demand r₂) (demand r)

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (demand p) = demand (⊎-comm p)
  comm (offerₗ σ) = offerᵣ (⊎-comm σ)
  comm (offerᵣ σ) = offerₗ (⊎-comm σ)

  assoc : ∀ {a b ab c abc} → Split a b ab → Split ab c abc → ∃ λ bc → (Split a bc abc) × (Split b c bc)
  assoc (offerₗ σ₁) (offerₗ σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₂ σ₁ in -, offerₗ σ₃ , demand (⊎-comm σ₄)
  assoc (offerᵣ σ₁) (offerₗ σ₂) =
    let _ , σ₃ , σ₄ = ⊎-unassoc σ₁ σ₂ in -, offerᵣ σ₃ , offerₗ σ₄
  assoc (demand σ₁) (offerᵣ σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₁) σ₂ in -, offerᵣ σ₄ , offerᵣ σ₃
  assoc (demand σ₁) (demand σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in -, demand σ₃ , demand σ₄
  instance auth-raw-sep : RawSep (Market A)
  RawSep._⊎_≣_ auth-raw-sep = Split

  instance auth-has-sep : IsSep auth-raw-sep
  auth-has-sep = record
    { ⊎-comm  = comm
    ; ⊎-assoc = assoc
    }

  instance auth-sep : Separation _
  auth-sep = record
    { isSep = auth-has-sep }

module _ {a} {{ s : UnitalSep a }} where

  open UnitalSep s using () renaming (Carrier to A)

  module U = IsUnitalSep
  instance auth-is-unital : IsUnitalSep auth-raw-sep (demand ε)
  U.isSep auth-is-unital  = auth-has-sep
  U.⊎-idˡ auth-is-unital {offer l} = offerᵣ ⊎-idˡ
  U.⊎-idˡ auth-is-unital {demand r} = demand ⊎-idˡ
  U.⊎-id⁻ˡ auth-is-unital (offerᵣ σ) = cong offer (sym (⊎-id⁻ˡ σ))
  U.⊎-id⁻ˡ auth-is-unital (demand σ) = cong demand (⊎-id⁻ˡ σ)


module _ {a} {{ s : MonoidalSep a }} where

  open MonoidalSep s using () renaming (Carrier to A)

  match : ∀ {a b : A} {c d} → (demand a) ⊎ (offer b) ≣ c → (demand (d ∙ a)) ⊎ (offer (d ∙ b)) ≣ c
  match (offerᵣ σ) = offerᵣ (⊎-∙ₗ σ)

module _ {ℓ} {A : Set ℓ} {{_ : RawSep A}} where

  private
    variable
      ℓv : Level
      P Q : Pred (A × A) ℓv

  data ● {p} (P : Pred (A × A) p) : Pred (Market A) (ℓ ⊔ p) where
    lift : ∀ {r l₁ l₂} → P (l₁ , r) → r ⊎ l₂ ≣ l₁ → ● P (offer l₂)

  ●-map : ∀[ P ⇒ Q ] → ∀[ ● P ⇒ ● Q ]
  ●-map f (lift px le) = lift (f px) le

module _ {ℓ} {A : Set ℓ} where

  private
    variable
      ℓv : Level
      P Q : Pred A ℓv

  data ○ {p} (P : Pred A p) : Pred (Market A) p where
    frag : ∀ {x} → P x → ○ P (demand x)

  ○-map : ∀[ P ⇒ Q ] → ∀[ ○ P ⇒ ○ Q ]
  ○-map f (frag px) = frag (f px)

-- {- Completion preserving updates -}
-- module _ {a} {{s : UnitalSep a}} where

--   open UnitalSep s renaming (Carrier to A)

--   open import Relation.Unary.Separation.Construct.Product

--   ⟰ : ∀ {p} → (P : Pred (A × A) p) → Pred (A × A) (a ⊔ p)
--   ⟰ P (a , b) = ∀ {φ} → (completes : b ⊎ φ ≣ a) → ∃₂ λ a' b' → b' ⊎ φ ≣ a' × P (a' , b')

--   {- Updating Market A using updates in A × A -}
--   offer-update : ∀ {p q} → {P : Pred (A × A) p} {Q : Pred (A × A) q} →
--              ∀[ P ⇒ ⟰ Q ] → ∀[ offer P ⇒ ⤇ (offer Q) ]
--   offer-update f (lift px le) = local λ where
--     (on-left fr refl) →
--       let _ , _ , σ , qx = f px le
--       in -, -, on-left fr refl , lift qx σ
