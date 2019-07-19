-- | An implementation of the Authoritative PCM
module Relation.Unary.Separation.Construct.Auth (A : Set) where

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
    _◐_ : ∀ (x y : A) → Auth
    ◌   : ∀ (x : A) → Auth

  data Split : Auth → Auth → Auth → Set where

    on-left : ∀ {x y y' z } →
               y ⊎ y' ≣ z →
               z ≤ x →
               Split (x ◐ y) (◌ y') (x ◐ z)

    on-right  : ∀ {x y y' z} →
               y ⊎ y' ≣ z →
               z ≤ x →
               Split (◌ y') (x ◐ y) (x ◐ z)

    neither  : ∀ {y y' z} →
               y ⊎ y' ≣ z →
               Split (◌ y) (◌ y') (◌ z)

  data ● {p} (P : Pred Auth p) : Pred Auth  p where
    whole : ∀ {x y} → P (x ◐ y) → ● P (x ◐ y)

  data ○ {p} (P : Pred A p) : Pred Auth p where
    frag : ∀ {x} → P x → ○ P (◌ x)

  open RawSep
  instance auth-raw-sep : RawSep Auth
  _⊎_≣_ auth-raw-sep = Split

  instance auth-raw-unital : RawUnitalSep Auth
  auth-raw-unital = record { ε = ◌ ε ; sep = auth-raw-sep }

module _ ⦃ A-sep : RawUnitalSep A ⦄ ⦃ _ : IsSep (RawUnitalSep.sep A-sep) ⦄ where
  open IsSep ⦃...⦄
  open RawSep ⦃...⦄
  open RawUnitalSep ⦃...⦄

  private instance A-raw = RawUnitalSep.sep A-sep

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (on-right l r) = on-left l r
  comm (on-left l r)  = on-right l r
  comm (neither x)    = neither (⊎-comm x)

  assoc : ∀ {Φ₁ Φ₂ Ψ₁ Ψ₂ Ψ₃} → Split Φ₁ Φ₂ Ψ₁ → Split Ψ₁ Ψ₂ Ψ₃ →
          ∃ (λ ξ → Split Φ₁ ξ Ψ₃ × Split Φ₂ Ψ₂ ξ)
  assoc (on-left s r) (on-left s' r') =
    let _ , q , p = ⊎-assoc s s' in -, on-left q r' , (neither p)
  assoc (on-right s l) (on-left s' l') with ⊎-assoc (⊎-comm s) s'
  ... | a , q , p =
    let le = ≤-trans (-, ⊎-comm q) l' 
    in -, on-right (⊎-comm q) l' , on-left p le
  assoc (neither s) (on-right s' l) with ⊎-assoc s (⊎-comm s')
  ... | a , q , p =
    let le = ≤-trans (-, ⊎-comm q) l
    in -, on-right (⊎-comm q) l , on-right (⊎-comm p) le
  assoc (neither s) (neither s') =
    let _ , p , q = ⊎-assoc s s' in -, neither p , neither q

  instance auth-has-sep : IsSep auth-raw-sep
  auth-has-sep = record
    { ⊎-comm  = comm
    ; ⊎-assoc = assoc
    }

  instance auth-sep : Separation _ _
  auth-sep = record
    { set   = P.setoid Auth
    ; isSep = auth-has-sep }

  -- ○ is a relative functor of sorts
  ○-map : ∀ {p q} {P : Pred A p}{Q : Pred A q} {Φ} → (P ─✴ Q) Φ → (○ P ─✴ ○ Q) (◌ Φ)
  ○-map f (frag p) (neither σ) = frag (f p σ)

-- The thing is not quite unital, because the inclusion between a part and the whole
-- is part of the split relation and does not necessarily hold for a given carrier pair.
-- If we force the authoratative carrier pair to witness the inclusion,
-- then other things break, because that witness doesn't neccessarily agree with
-- the inclusion as part of the split relation...

-- module _ ⦃ _ : IsUnitalSep {C = A} _≡_ ⦄  where
--   open IsUnitalSep ⦃...⦄
--   open RawUnitalSep unital 
--   instance _ = unital
--   instance _ = isSep

  -- module U = IsUnitalSep
  -- instance auth-is-unital : IsUnitalSep {C = Auth} _≡_
  -- U.unital auth-is-unital                           = auth-raw-unital
  -- U.isSep auth-is-unital                            = auth-has-sep
  -- U.⊎-identityˡ auth-is-unital {x ◐  y x₁} refl = {!!} -- on-right {!!} {!!} (⊎-identityʳ refl)
  -- U.⊎-identityˡ auth-is-unital {◌ x} refl      = neither (⊎-identityˡ refl)
  -- U.⊎-identity⁻ˡ auth-is-unital (on-right x) rewrite ⊎-identity⁻ʳ x = refl
  -- U.⊎-identity⁻ˡ auth-is-unital (neither x) rewrite ⊎-identity⁻ˡ x  = refl 
  -- U.ε-separateˡ auth-is-unital (neither x)          = cong ◌ (ε-separateˡ x)
