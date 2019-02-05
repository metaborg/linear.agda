module Sessions.Syntax.Types where

open import Level
open import Size
open import Function

open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Codata.Thunk

open import Algebra

open import Relation.Unary hiding (_∈_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as DecM
open import Relation.Nullary.Product
open import Relation.Binary.PropositionalEquality as P hiding ([_])

open import Relation.Unary.Separation

{- Unrestricted-, Session- and Expression types-}
module _ where
  mutual
    data UType : Size → Set where
      unit  : ∀[ UType ] 
      _⟶_  : ∀[ Type ⇒ Type ⇒ UType ]
      prod  : ∀[ UType ⇒ UType ⇒ UType ]

    -- channel types
    data SType : Size →  Set where
      -- input and output
      -- a ⊗ α : output a and continue as α
      -- a ⅋ α : input a and continue as α
      _⊗_ _⅋_ : ∀[ Type ⇒ Thunk SType ⇒ SType ]

      -- selection and choice
      -- a ⊕ b : select from a and b
      -- a ⅋ b : offer choice of a and b
      _⊕_ _&_ : ∀[ Type ⇒ Thunk SType ⇒ SType ]

      -- terminate
      end! end? : ∀[ SType ]

    data Type : Size → Set where
      unit  : ∀[ Type ] 
      _⟶_  : ∀[ Type ⇒ Type ⇒ Type ]
      chan  : ∀[ SType ⇒ Type ]
      prod  : ∀[ Type ⇒ Type ⇒ Type ]
      _⊸_   : ∀[ Type ⇒ Type ⇒ Type ]

{- Contexts -}
module _ where
  ICtx = List (UType ∞) -- intuitionistic
  LCtx = List (Type ∞)  -- linear

  Ctx : Set
  Ctx = ICtx × LCtx

  separation : RawSeparation Ctx
  separation = record
    { ε = [] , []
    ; _⊎_≣_ = λ where
      (Γ₁ , Φ₁) (Γ₂ , Φ₂) (Γ , Φ) → (Γ₁ ≡ Γ × Γ₂ ≡ Γ) × Interleaving Φ₁ Φ₂ Φ }

  _ctx-≡_ : Ctx → Ctx → Set
  _ctx-≡_  = Pointwise _≡_ _↭_

  postulate isSeparation : IsSeparation _ctx-≡_ separation

  ctx-resource : Separation _ _
  ctx-resource = record
    { set = record
        { Carrier = Ctx
        ; _≈_ = _ctx-≡_
        ; isEquivalence = ×-isEquivalence isEquivalence ↭-isEquivalence }
    ; raw = separation
    ; isSeparation = isSeparation }

  open Separation ctx-resource public hiding (isSeparation)

{- Some conventions -}
variable
  u v w   : UType ∞
  a b c   : Type ∞
  α β γ   : SType ∞
  Γ Γ₁ Γ₂ : ICtx

{- Duality -}
module _ where

  infixl 1000 _⁻¹
  _⁻¹  : ∀[ SType ⇒ SType ]
  (a ⊗ β) ⁻¹ = a ⅋ λ where .force → (force β) ⁻¹
  (a ⅋ β) ⁻¹ = a ⊗ λ where .force → (force β) ⁻¹
  (a ⊕ β) ⁻¹ = a & λ where .force → (force β) ⁻¹
  (a & β) ⁻¹ = a ⊕ λ where .force → (force β) ⁻¹
  end! ⁻¹    = end?
  end? ⁻¹    = end!

{- Derivative of a session type -}
module _ where

  data Δ : SType ∞ → List (Type ∞) → SType ∞ → Set where
    {- Todo -}

{- Subset of unrestricted types -}
module _ where

  li : ∀[ UType ⇒ Type ]
  li unit = unit
  li (a ⟶ b) = a ⟶ b
  li (prod a b) = prod (li a) (li b)

  IsUnr : Type ∞ → Set
  IsUnr a = ∃ λ u → li u ≡ a

  isUnr? : Decidable IsUnr
  isUnr? unit = yes (unit , P.refl)
  isUnr? (a₁ ⟶ a₂) = yes ((a₁ ⟶ a₂) , P.refl)
  isUnr? (chan x) = no λ where
    (unit , ())
    (_ ⟶ _ , ())
    (prod _ _ , ())
  isUnr? (prod a₁ a₂) = DecM.map′
    (λ where ((u , P.refl) , (v , P.refl)) → prod u v , P.refl)
    (λ where
      (unit , ())
      (_ ⟶ _ , ())
      (prod a b , P.refl) → (a , P.refl) , (b , P.refl))
        ((isUnr? a₁) ×-dec (isUnr? a₂))
  isUnr? (a₁ ⊸ a₂) = no λ where
    (unit , ())
    (_ ⟶ _ , ())
    (prod _ _ , ())

{- context construction and transformations -}
module _ where
  _∷ᵢ_ : UType ∞ → Ctx → Ctx
  a ∷ᵢ (Γ , Φ) = (a ∷ Γ) , Φ

  _∷ₗ_ : Type ∞ → Ctx → Ctx
  a ∷ₗ (Γ , Φ) = Γ , a ∷ Φ

  CtxTf = Ctx → Ctx

  infixr 20 _◂_
  _◂_ : Type ∞ → CtxTf → CtxTf
  (a ◂ f) Δ with isUnr? a
  ... | yes (u , P.refl) = u ∷ᵢ f Δ
  ... | no  ¬u           = a ∷ₗ f Δ

{- Linearly a Singleton  -}
module _ {p} (P : Pred (Type ∞) p) where

  data Only : SPred p where
    only : ∀ {a} → P a → Only (a ∷ₗ ε)

{- Linear membership -}
module _ where

  Exactly : Type ∞ → SPred _
  Exactly = Only ∘ _≡_

{- membership -}
module _ where

  _∈ᵢ_ : UType ∞ → Ctx → Set
  a ∈ᵢ (Γ , _) = a ∈ Γ

  _∈ₗ_ : Type ∞ → Ctx → Set
  a ∈ₗ (_ , Φ) = a ∈ Φ
