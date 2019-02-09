module Sessions.Syntax.Types where

open import Level
open import Size
open import Function

open import Data.Bool
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
open import Relation.Unary.Separation.Construct.Product
open UnitalSep ⦃...⦄ hiding (isSep; isEquivalence; SPred)

{- Unrestricted-, Session- and Expression types-}
module _ where
  mutual
    data UType : Size → Set where
      unit  : ∀[ UType ] 
      prod  : ∀[ UType ⇒ UType ⇒ UType ]
      -- _⟶_  : ∀[ Type ⇒ Type ⇒ UType ]

    -- channel types
    infixr 10 _⅋_
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
      -- _⟶_  : ∀[ Type ⇒ Type ⇒ Type ]
      chan  : ∀[ SType ⇒ Type ]
      prod  : ∀[ Type ⇒ Type ⇒ Type ]
      _⊸_   : ∀[ Type ⇒ Type ⇒ Type ]

{- Contexts -}
module _ where

  LCtx = List (Type ∞)   -- linear
  SCtx = List (SType ∞)  -- sessions

{- Separation of contexts -}
module _ {t} {T : Set t} where

  private
    Ctx : Set t
    Ctx = List T

  separation : RawSep Ctx
  separation = record { _⊎_≣_ = Interleaving }

  postulate ctx-hasUnitalSep  : IsUnitalSep _↭_ separation

  instance
    ctx-resource : UnitalSep _ _
    ctx-resource = record
      { set = record { isEquivalence = ↭-isEquivalence }
      ; isUnitalSep = ctx-hasUnitalSep }

  LPred : (p : Level) → Set (t ⊔ Level.suc p)
  LPred p = Ctx → Set p

  {- Linearly a Singleton  -}
  module _ {p} (P : Pred T p) where

    data Only : LPred p where
      only : ∀ {a} → P a → Only (a ∷ ε)

  module _ where

    Just : T → LPred t
    Just t = Exactly (t ∷ ε)

{- Some conventions -}
variable
  u v w   : UType ∞
  a b c   : Type ∞
  α β γ   : SType ∞

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
  li (prod a b) = prod (li a) (li b)
  -- li (a ⟶ b) = a ⟶ b

  IsUnr : Type ∞ → Set
  IsUnr a = ∃ λ u → li u ≡ a

  isUnr? : Decidable IsUnr
  isUnr? unit = yes (unit , P.refl)
  -- isUnr? (a₁ ⟶ a₂) = yes ((a₁ ⟶ a₂) , P.refl)
  isUnr? (chan x) = no λ where
    (unit , ())
    (prod _ _ , ())
  isUnr? (prod a₁ a₂) = DecM.map′
    (λ where ((u , P.refl) , (v , P.refl)) → prod u v , P.refl)
    (λ where
      (unit , ())
      (prod a b , P.refl) → (a , P.refl) , (b , P.refl))
        ((isUnr? a₁) ×-dec (isUnr? a₂))
  isUnr? (a₁ ⊸ a₂) = no λ where
    (unit , ())
    (prod _ _ , ())

{- context construction and transformations -}
-- module _ where
--   _∷ᵢ_ : UType ∞ → Ctx → Ctx
--   a ∷ᵢ (Γ , Φ) = (a ∷ Γ) , Φ

--   _∷ₗ_ : Type ∞ → Ctx → Ctx
--   a ∷ₗ (Γ , Φ) = Γ , a ∷ Φ

  CtxTf = LCtx → LCtx

  infixr 20 _◂_
  _◂_ : Type ∞ → CtxTf → CtxTf
  (a ◂ f) Δ = a ∷ f Δ

{- membership -}
-- module _ where

--   _∈ᵢ_ : UType ∞ → Ctx → Set
--   a ∈ᵢ (Γ , _) = a ∈ Γ

--   _∈ₗ_ : Type ∞ → Ctx → Set
--   a ∈ₗ (_ , Φ) = a ∈ Φ
