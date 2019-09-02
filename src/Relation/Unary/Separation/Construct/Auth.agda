{-# OPTIONS --allow-unsolved-metas #-}

-- | An implementation of the Authoritative PCM
module Relation.Unary.Separation.Construct.Auth (A : Set) where

open import Level hiding (Lift)
open import Data.Product
open import Data.Maybe

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

module _ {{ A-sep : RawSep A }} where

  data Auth : Set where
    ◐ : ∀ {r l p : A} → r ⊎ l ≣ p → Auth
    ◌ : ∀ (r : A) → Auth

module _ {{ sep : RawSep A }} {{ _ : IsSep sep }} where

  lem : ∀ {x y z : A} (p : x ≤ y) → (z ≤ rem p) → ∃ λ z' → x ⊎ z ≣ z' × z' ≤ y
  lem (_ , p) (_ , q) = let z , r , s = ⊎-unassoc p q in z , r , (-, s)

  data Split : Auth → Auth → Auth → Set where

    on-left : ∀ {r₁ r₂ l₁ l₂ p}
              {σ₁ : r₁ ⊎ l₁ ≣ p} →
              (σ₂ : r₂ ⊎ l₂ ≣ l₁) →
              let _ , _ , σ = ⊎-assoc σ₂ (⊎-comm σ₁) in
              Split (◐ σ₁) (◌ r₂) (◐ σ)

    on-right : ∀ {r₁ r₂ l₁ l₂ p}
               {σ₁ : r₁ ⊎ l₁ ≣ p} →
               (σ₂ : r₂ ⊎ l₂ ≣ l₁) →
               let _ , _ , σ = ⊎-assoc σ₂ (⊎-comm σ₁) in
               Split (◌ r₂) (◐ σ₁) (◐ σ)

    neither  : ∀ {y y' z} →
               y ⊎ y' ≣ z →
               Split (◌ y) (◌ y') (◌ z)

module _ {{s : RawSep A}} {{ _ : IsUnitalSep s }} where

  data ● {p} (P : Pred A p) : Pred Auth p where
    whole : ∀ {x} → P x → ● P (◐ {r = x} ⊎-idʳ)

  data ○ {p} (P : Pred A p) : Pred Auth p where
    frag : ∀ {x} → P x → ○ P (◌ x)

  data Lift {p} (P : A × A → Set p) : Pred Auth p where
    lift : ∀ {p r l} → P (p , r) → ∀ le → Lift P (◐ {r} {l} {p} le)

  instance auth-raw-sep : RawSep Auth
  RawSep._⊎_≣_ auth-raw-sep = Split

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (on-right l) = {!!}
  comm (on-left l)  = {!!}
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

  postulate assoc : ∀ {Φ₁ Φ₂ Ψ₁ Ψ₂ Ψ₃} → Split Φ₁ Φ₂ Ψ₁ → Split Ψ₁ Ψ₂ Ψ₃ →
                    ∃ (λ ξ → Split Φ₁ ξ Ψ₃ × Split Φ₂ Ψ₂ ξ)
  -- assoc (on-left (n , s) refl) (on-left (m , s') refl) =
  --   let _ , q , p = ⊎-unassoc s s' in
  --   -, subst (Split _ _) {!!} (on-left (-, p) refl) , neither q
  -- assoc
  --   (on-right {q = s₄} {le = r , s''} (n , s) refl)
  --   (on-left {le = r' , s'''} (m , s') eq') with resplit s₄ s' s''' | ⊎-unassoc s (⊎-comm s')
  -- ... | ac , bd , p1 , p2 , p3 | wut , p4 , p5 = ◐ _ ac (-, p3) , on-right (-, p2) {!refl!} , on-left (-, ⊎-comm p5) {!refl!}
  {-
    (z , _ , p) 
      ≡
    let z' , r , s = ⊎-assoc (⊎-comm p3) (⊎-comm p2) in z' , (⊎-comm s) , (-, ⊎-comm r)
      ≡
    let z' , r , s = ⊎-unassoc p3 p2 in z' , r , (-, s)
      ≡
    lem (bd , p3) (m , p2)
  -}
  -- assoc (neither s) (on-right s' eq) = {!!} -- with ⊎-assoc s (⊎-comm s')
  -- ... | a , q , p =
    -- let le = ≤-trans (-, ⊎-comm q) l
    -- in -, on-right (⊎-comm q) l , on-right (⊎-comm p) le
  -- assoc (neither s) (neither s') =
  --   let _ , p , q = ⊎-assoc s s' in -, neither p , neither q

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

  module U = IsUnitalSep
  instance auth-is-unital : IsUnitalSep auth-raw-sep
  U.ε auth-is-unital      = ◌ ε
  U.isSep auth-is-unital  = auth-has-sep
  U.⊎-idˡ auth-is-unital {◐ x} = {!on-right ?!}
  U.⊎-idˡ auth-is-unital {◌ r} = neither ⊎-idˡ
  U.⊎-id⁻ˡ auth-is-unital (on-right σ) with ⊎-id⁻ˡ σ 
  ... | refl = {!!}
  U.⊎-id⁻ˡ auth-is-unital (neither σ) = cong ◌ (⊎-id⁻ˡ σ)

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
  -- U.⊎-idˡ auth-is-unital {x ◐  y x₁} refl = {!!} -- on-right {!!} {!!} (⊎-idʳ refl)
  -- U.⊎-idˡ auth-is-unital {◌ x} refl      = neither (⊎-idˡ refl)
  -- U.⊎-id⁻ˡ auth-is-unital (on-right x) rewrite ⊎-id⁻ʳ x = refl
  -- U.⊎-id⁻ˡ auth-is-unital (neither x) rewrite ⊎-id⁻ˡ x  = refl 
  -- U.ε-separateˡ auth-is-unital (neither x)          = cong ◌ (ε-separateˡ x)
