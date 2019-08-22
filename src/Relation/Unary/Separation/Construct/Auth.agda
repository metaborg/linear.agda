-- | An implementation of the Authoritative PCM
module Relation.Unary.Separation.Construct.Auth (A : Set) where

open import Level hiding (Lift)
open import Data.Product
open import Data.Maybe

import Data.Sum as Sum

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

module _ {{ A-sep : RawSep A }} where

  data Auth : Set where
    ◐ : ∀ (x y : A) → y ≤ x → Auth
    ◌ : ∀ (x : A) → Auth

module _ {{ sep : RawSep A }} {{ _ : IsSep sep }} where

  lem : ∀ {x y z : A} (p : x ≤ y) → (z ≤ rem p) → ∃ λ z' → x ⊎ z ≣ z' × z' ≤ y
  lem (_ , p) (_ , q) = let z , r , s = ⊎-unassoc p q in z , r , (-, s)

  data Split : Auth → Auth → Auth → Set where

    on-left : ∀ {x y y' z q p} {le : y ≤ x} →
               (le' : y' ≤ rem le) →
               (z , q , p) ≡ lem le le' →
               Split (◐ x y le) (◌ y') (◐ x z p)

    on-right  : ∀ {x y y' z q p} {le : y ≤ x} →
               (le' : y' ≤ rem le) →
               (z , q , p) ≡ lem le le' →
               Split (◌ y') (◐ x y le) (◐ x z p)

    neither  : ∀ {y y' z} →
               y ⊎ y' ≣ z →
               Split (◌ y) (◌ y') (◌ z)

module _ {{s : RawUnitalSep A}} ⦃ _ : IsUnitalSep s ⦄ where

  data ● {p} (P : Pred A p) : Pred Auth p where
    whole : ∀ {x} → P x → ● P (◐ x ε ε-minimal)

  data ○ {p} (P : Pred A p) : Pred Auth p where
    frag : ∀ {x} → P x → ○ P (◌ x)

  data Lift {p} (P : A → A → Set p) : Pred Auth p where
    lift : ∀ {x y} → P x y → (le : y ≤ x) → Lift P (◐ x y le)

  open RawSep
  instance auth-raw-sep : RawSep Auth
  _⊎_≣_ auth-raw-sep = Split

  instance auth-raw-unital : RawUnitalSep Auth
  auth-raw-unital = record { ε = ◌ ε ; sep = auth-raw-sep }

module _ ⦃ A-sep : RawUnitalSep A ⦄ ⦃ _ : IsUnitalSep A-sep ⦄ where

  private instance A-raw = RawUnitalSep.sep A-sep

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (on-right l refl) = on-left l refl
  comm (on-left l refl)  = on-right l refl
  comm (neither x)  = neither (⊎-comm x)

  {-
     cong (λ z → ⊎-comm (proj₁ (proj₂ z)))

         ⊎-assoc 
             (⊎-comm (⊎-comm (proj₁ (proj₂ (⊎-assoc (⊎-comm  s') (⊎-comm  s)))))) 
             (⊎-comm  (proj₂ le))

       ↓⟨ elim double ⊎-comm ⟩

         ⊎-assoc 
             (proj₁ (proj₂ (⊎-assoc (⊎-comm  s') (⊎-comm  s)))) 
             (⊎-comm  (proj₂ le))

         ⊎-assoc 
             (⊎-comm s')
             (proj₁ (proj₂ (⊎-assoc (⊎-comm  s) (⊎-comm (proj₂ le)))))

       ↑⟨ elim double ⊎-comm ⟩

         ⊎-assoc 
             (⊎-comm s')
             (⊎-comm (⊎-comm (proj₁ (proj₂ (⊎-assoc (⊎-comm  s) (⊎-comm  (proj₂ le)))))))
  -}

  assoc : ∀ {Φ₁ Φ₂ Ψ₁ Ψ₂ Ψ₃} → Split Φ₁ Φ₂ Ψ₁ → Split Ψ₁ Ψ₂ Ψ₃ →
          ∃ (λ ξ → Split Φ₁ ξ Ψ₃ × Split Φ₂ Ψ₂ ξ)
  assoc (on-left (n , s) refl) (on-left (m , s') refl) =
    let _ , q , p = ⊎-unassoc s s' in
    -, subst (Split _ _) {!!} (on-left (-, p) refl) , neither q
  assoc
    (on-right {q = s₄} {le = r , s''} (n , s) refl)
    (on-left {le = r' , s'''} (m , s') eq') with resplit s₄ s' s''' | ⊎-unassoc s (⊎-comm s')
  ... | ac , bd , p1 , p2 , p3 | wut , p4 , p5 = ◐ _ ac (-, p3) , on-right (-, p2) {!refl!} , on-left (-, ⊎-comm p5) {!refl!}
  {-
    (z , _ , p) 
      ≡
    let z' , r , s = ⊎-assoc (⊎-comm p3) (⊎-comm p2) in z' , (⊎-comm s) , (-, ⊎-comm r)
      ≡
    let z' , r , s = ⊎-unassoc p3 p2 in z' , r , (-, s)
      ≡
    lem (bd , p3) (m , p2)
  -}
  assoc (neither s) (on-right s' eq) = {!!} -- with ⊎-assoc s (⊎-comm s')
  -- ... | a , q , p =
    -- let le = ≤-trans (-, ⊎-comm q) l
    -- in -, on-right (⊎-comm q) l , on-right (⊎-comm p) le
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

--   module U = IsUnitalSep
--   instance auth-is-unital : IsUnitalSep auth-raw-unital
--   U.isSep auth-is-unital                            = auth-has-sep
--   U.⊎-identityˡ auth-is-unital {◐ x y l} refl = on-right (⊎-identityʳ refl) l
--   U.⊎-identityˡ auth-is-unital {◌ x} refl      = neither (⊎-identityˡ refl)

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
