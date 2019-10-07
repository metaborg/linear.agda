-- | An implementation of the Marketoritative PCM
module Relation.Unary.Separation.Construct.Market where

open import Level hiding (Lift)
open import Data.Product

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Unary.Separation
open import Relation.Unary.Separation.Morphisms

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
  instance market-raw-sep : RawSep (Market A)
  RawSep._⊎_≣_ market-raw-sep = Split

  instance market-has-sep : IsSep market-raw-sep
  market-has-sep = record
    { ⊎-comm  = comm
    ; ⊎-assoc = assoc
    }

  instance market-sep : Separation _
  market-sep = record
    { isSep = market-has-sep }

module _ {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }} where

  module U = IsUnitalSep
  instance market-is-unital : IsUnitalSep market-raw-sep (demand ε)
  U.isSep market-is-unital  = market-has-sep
  U.⊎-idˡ market-is-unital {offer l} = offerᵣ ⊎-idˡ
  U.⊎-idˡ market-is-unital {demand r} = demand ⊎-idˡ
  U.⊎-id⁻ˡ market-is-unital (offerᵣ σ) = cong offer (sym (⊎-id⁻ˡ σ))
  U.⊎-id⁻ˡ market-is-unital (demand σ) = cong demand (⊎-id⁻ˡ σ)


module _ {a} {{ s : MonoidalSep a }} where

  open MonoidalSep s using () renaming (Carrier to A)

  matching : ∀ {a b : A} {c d} → (demand a) ⊎ (offer b) ≣ c → (demand (d ∙ a)) ⊎ (offer (d ∙ b)) ≣ c
  matching (offerᵣ σ) = offerᵣ (⊎-∙ₗ σ)

module _ {ℓ} {A : Set ℓ} {{_ : RawSep A}} where

  private
    variable
      ℓv : Level
      P Q : Pred (A × A) ℓv
        
  [_]Completes : A → (A × A) → Set ℓ
  [_]Completes x (y , z) = x ⊎ z ≣ y

  data ● {p} (P : Pred (A × A) p) : Pred (Market A) (ℓ ⊔ p) where
    lift : ∀ {xs l₂} → P xs → [ l₂ ]Completes xs → ● P (offer l₂)

  ●-map : ∀[ P ⇒ Q ] → ∀[ ● P ⇒ ● Q ]
  ●-map f (lift px le) = lift (f px) le

module _ {a} (A : Set a) {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}} where

  open Morphism

  market : Morphism s₁ market-sep
  j market                 = demand
  j-map market s           = demand s
  j-⊎ market (demand σ)    = -, refl
  j-map⁻ market (demand σ) = σ

module _ {a} {A : Set a} {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}} where

  open import Relation.Unary.Separation.Construct.Product
  open Morphism (market A)

  data ○ {p} (P : Pred (A × A) p) : Pred (Market A) (p) where
    lift : ∀ {xs} → P (ε , xs) → ○ P (demand xs)

  ○≺●ₗ : ∀ {p q} {P : Pred A p} {Q : Pred (A × A) q} → ∀[ P ⇒ⱼ ● Q ─✴ ● (Π₂ P ✴ Q) ]
  app (○≺●ₗ px) (lift qx σ₂) (offerᵣ σ₁) with ⊎-assoc (⊎-comm σ₁) σ₂
  ... | _ , σ₃ , σ₄ = lift (snd px ×⟨ ⊎-idˡ , σ₄ ⟩ qx ) σ₃

  ○≺●ᵣ : ∀ {p q} {P : Pred A p} {Q : Pred (A × A) q} → ∀[ ● (Π₂ P ✴ Q) ⇒ J P ✴ ● Q ]
  ○≺●ᵣ (lift (snd px ×⟨ σₗ , σᵣ ⟩ qx) σ₂) with ⊎-id⁻ˡ σₗ
  ... | refl with ⊎-unassoc σ₂ σᵣ
  ... | _ , σ₃ , σ₄ = inj px ×⟨ offerᵣ (⊎-comm σ₃) ⟩ lift qx σ₄

{- Complete with respect to a certain element -}
module _ {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }} where

  open import Relation.Unary.Separation.Construct.Product
  open Morphism (market A)

  record _◑_ {p q} (P : Pred A p) (Q : Pred (A × A) q) (Φ : A × A) : Set (a ⊔ p ⊔ q) where
    constructor _◑⟨_⟩_
    field
      {Φp Φq} : _
      px  : P Φp
      inc : proj₁ Φ ⊎ Φp ≣ Φq
      qx  : Q (Φq , proj₂ Φ)

  -- the following cannot be proven unfortunately
  -- _ : ∀[ (P ◑ Q₁) ✴ Q₂ ⇒ P ◑ (Q₁ ✴ Q₂) ]

  absorb : ∀ {p q} {P : Pred A p} {Q : Pred (A × A) q} →
           ∀[ P ⇒ⱼ ● Q ─✴ ● (P ◑ Q) ]
  app (absorb px) (lift qx k) (offerᵣ σ) with ⊎-assoc (⊎-comm σ) k
  ... | _ , σ₂ , σ₃ with ⊎-unassoc σ₂ (⊎-comm σ₃)
  ... | _ , σ₄ , σ₅ = lift (px ◑⟨ σ₅ ⟩ qx) σ₄

  expell : ∀ {p q} {P : Pred A p} {Q : Pred (A × A) q} →
           ∀[ ● (P ◑ Q) ⇒ J P ✴ ● Q ]
  expell (lift (px ◑⟨ τ₁ ⟩ qx) k) with ⊎-unassoc (⊎-comm τ₁) k
  ... | _ , τ₃ , τ₄ = (inj px) ×⟨ offerᵣ τ₃ ⟩ (lift qx τ₄)

{- Completion preserving updates -}
module _ {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }} where

  open import Relation.Unary.Separation.Construct.Product

  record ⟰_ {p} (P : Pred (A × A) p) (Φᵢ : A × A) : Set (a ⊔ p) where
    field
      updater : ∀ {Φⱼ Φₖ} →
                Φᵢ ⊎ Φⱼ ≣ (Φₖ , Φₖ) →
                ∃₂ λ Φₗ Φ → Φₗ ⊎ Φⱼ ≣ (Φ , Φ) × P Φₗ
  open ⟰_ public

  ●-update : ∀ {p q} {P : Pred (A × A) p} {Q : Pred (A × A) q} →
             ∀[ ○ (P ─✴ ⟰ Q) ⇒ ● P ─✴ ● Q ]
  app (●-update (lift f)) (lift px σ₁) (offerᵣ σ₂) with ⊎-assoc (⊎-comm σ₂) σ₁
  ... | _ , σ₃ , σ₄ with updater (app f px (⊎-idˡ , σ₄)) (⊎-idʳ , ⊎-comm σ₃)
  ... | _ , _ , (σ₅ , σ₆) , qx with ⊎-id⁻ʳ σ₅
  ... | refl = lift qx (⊎-comm σ₆)
