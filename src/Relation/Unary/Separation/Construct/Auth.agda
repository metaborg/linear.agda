-- | An implementation of the Authoritative PCM
module Relation.Unary.Separation.Construct.Auth {A : Set} where

open import Level
open import Data.Product
open import Data.Maybe

import Data.Sum as Sum

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

module _ ⦃ A-sep : RawUnitalSep A ⦄ where
  open RawUnitalSep A-sep
  open RawSep sep

  data Auth : Set where
    authed : ∀ (x y : A) → .(y ≤ x) → Auth
    unauth : ∀ (x : A) → Auth

  -- data ● {p} (P : Pred A p) : Pred Auth  p where
  --   authed   : ∀ {x} → P x → ● P (authed x ε {!ε-minimal!})

  -- data ○ {p} (P : Pred A p) : Pred Auth p where
  --   unauthed : ∀ {x} → P x → ○ P (nothing ◐ x)

  data Split : Auth → Auth → Auth → Set where

    on-left : ∀ {x y y' z } .{le le'} →
               y ⊎ y' ≣ z →
               Split (authed x y le) (unauth y') (authed x z le')

    on-right  : ∀ {x y y' z} .{le le'} →
               y ⊎ y' ≣ z →
               Split (unauth y') (authed x y le) (authed x z le')

    neither  : ∀ {y y' z} →
               y ⊎ y' ≣ z →
               Split (unauth y) (unauth y') (unauth z)

  -- ◐-invₗ : ∀ {x z Φₗ Φᵣ Φ} → Split Φ (unauth ◐ Φᵣ) (z ◐ Φ) → x ≡ z
  -- ◐-invₗ (on-left _ _) = refl
  -- ◐-invₗ (neither  _)  = refl

--   ◐-invᵣ : ∀ {x z Φₗ Φᵣ Φ} → Split (nothing ◐ Φₗ) (x ◐ Φᵣ) (z ◐ Φ) → x ≡ z
--   ◐-invᵣ (on-right _ _) = refl
--   ◐-invᵣ (neither  _)   = refl

--   frag-split : ∀ {Φₗ Φᵣ Φ} → Split Φₗ Φᵣ Φ → frag Φₗ ⊎ frag Φᵣ ≣ frag Φ
--   frag-split (on-right x x₁)  = x
--   frag-split (on-left x x₁) = x
--   frag-split (neither x)     = x

  open RawSep
  auth-raw-sep : RawSep Auth
  _⊎_≣_ auth-raw-sep = Split

--   auth-unital : RawUnitalSep Auth
--   auth-unital = record { ε = nothing ◐ ε ; sep = auth-raw-sep }

module _ ⦃ A-sep : RawUnitalSep A ⦄ ⦃ _ : IsSep _≡_ (RawUnitalSep.sep A-sep) ⦄ where
  open IsSep ⦃...⦄

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (on-right x) = on-left x
  comm (on-left x ) = on-right x
  comm (neither x)  = neither (⊎-comm x)

  assoc : ∀ {Φ₁ Φ₂ Ψ₁ Ψ₂ Ψ₃} →
                    Split Φ₁ Φ₂ Ψ₁ → Split Ψ₁ Ψ₂ Ψ₃ →
                    ∃ (λ ξ → Split Φ₂ Ψ₂ ξ × Split Φ₁ ξ Ψ₃)
  assoc (on-left s) (on-left s') =
    let _ , p , q = ⊎-assoc s s' in -, (neither p) , on-left q
  assoc (on-right s) (on-left {le' = le} s') with ⊎-assoc (⊎-comm s) s'
  ... | a , p , q =  -, on-left {le' = ≤-trans (-, ⊎-comm q) le} p , on-right (⊎-comm q)
  assoc (neither s) (on-right {le' = le} s') with ⊎-assoc s (⊎-comm s')
  ... | a , p , q = -, on-right {le' = ≤-trans (-, ⊎-comm q) le} (⊎-comm p) , on-right (⊎-comm q)
  assoc (neither s) (neither s') =
    let _ , p , q = ⊎-assoc s s' in -, neither p , neither q

  instance auth-has-sep : IsSep _≡_ auth-raw-sep
  auth-has-sep = record
    { ⊎-comm  = comm
    ; ⊎-assoc = assoc
    }

  auth-sep : Separation _ _
  auth-sep = record
    { set   = P.setoid Auth
    ; isSep = auth-has-sep }

module _ ⦃ _ : IsUnitalSep {C = A} _≡_ ⦄  where
  open IsUnitalSep ⦃...⦄
  open RawUnitalSep unital 
  instance _ = unital
  instance _ = isSep
    
  module U = IsUnitalSep
  instance auth-is-unital : IsUnitalSep {C = Auth} _≡_
  U.unital auth-is-unital                           = record { ε = unauth ε ; sep = auth-raw-sep }
  U.isSep auth-is-unital                            = auth-has-sep
  U.⊎-identityˡ auth-is-unital {authed x y x₁} refl = on-right (⊎-identityʳ refl)
  U.⊎-identityˡ auth-is-unital {unauth x} refl      = neither (⊎-identityˡ refl)
  U.⊎-identity⁻ˡ auth-is-unital (on-right x) rewrite ⊎-identity⁻ʳ x = refl
  U.⊎-identity⁻ˡ auth-is-unital (neither x) rewrite ⊎-identity⁻ˡ x  = refl 
  U.ε-separateˡ auth-is-unital (neither x)          = cong unauth (ε-separateˡ x)
