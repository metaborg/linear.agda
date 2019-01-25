module Sessions.Syntax.Types where

open import Level
open import Size
open import Function

open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Codata.Thunk

open import Relation.Unary hiding (_∈_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as DecM
open import Relation.Nullary.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

{- P. Wadler's variation on Gay & Vasconcelos's GV -}
mutual
  data UType : Size → Set where
    unit  : ∀[ UType ] 
    _⟶_  : ∀[ Type ⇒ Type ⇒ UType ]
    prod  : ∀[ UType ⇒ UType ⇒ UType ]

  data Type : Size → Set where
    unit  : ∀[ Type ] 
    _⟶_  : ∀[ Type ⇒ Type ⇒ Type ]
    chan  : ∀[ SType ⇒ Type ]
    prod  : ∀[ Type ⇒ Type ⇒ Type ]
    _⊸_   : ∀[ Type ⇒ Type ⇒ Type ]

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

-- contexts
ICtx = List (UType ∞) -- intuitionistic
LCtx = List (Type ∞)  -- linear
-- SCtx = List (Maybe (SType ∞))

Ctx : Set
Ctx = ICtx × LCtx

variable
  u v w   : UType ∞
  a b c   : Type ∞
  α β γ   : SType ∞
  Γ Γ₁ Γ₂ : ICtx
  Φ Φ₁ Φ₂ : LCtx

-- coerce a unrestricted type into a type
li : ∀[ UType ⇒ Type ]
li unit = unit
li (a ⟶ b) = a ⟶ b
li (prod a b) = prod (li a) (li b)

-- the dual of a session type
infixl 1000 _⁻¹
_⁻¹  : ∀[ SType ⇒ SType ]
(a ⊗ β) ⁻¹ = a ⅋ λ where .force → (force β) ⁻¹
(a ⅋ β) ⁻¹ = a ⊗ λ where .force → (force β) ⁻¹
(a ⊕ β) ⁻¹ = a & λ where .force → (force β) ⁻¹
(a & β) ⁻¹ = a ⊕ λ where .force → (force β) ⁻¹
end! ⁻¹    = end?
end? ⁻¹    = end!

IsEmp : Type ∞ → Set
IsEmp a = ∃ λ u → li u ≡ a

isEmp? : Decidable IsEmp
isEmp? unit = yes (unit , refl)
isEmp? (a₁ ⟶ a₂) = yes ((a₁ ⟶ a₂) , refl)
isEmp? (chan x) = no λ where
  (unit , ())
  (_ ⟶ _ , ())
  (prod _ _ , ())
isEmp? (prod a₁ a₂) = DecM.map′
  (λ where ((u , refl) , (v , refl)) → prod u v , refl)
  (λ where
    (unit , ())
    (_ ⟶ _ , ())
    (prod a b , refl) → (a , refl) , (b , refl))
  ((isEmp? a₁) ×-dec (isEmp? a₂))
isEmp? (a₁ ⊸ a₂) = no λ where
  (unit , ())
  (_ ⟶ _ , ())
  (prod _ _ , ())

Emp : Ctx → Set
Emp (Γ , Φ) = Φ ≡ []

Only : Type ∞ → Ctx → Set
Only a Δ = proj₂ Δ ≡ [ a ]

_∈ᵢ_ : UType ∞ → Ctx → Set
a ∈ᵢ (Γ , _) = a ∈ Γ

_∈ₗ_ : Type ∞ → Ctx → Set
a ∈ₗ (_ , Φ) = a ∈ Φ

_∷ᵢ_ : UType ∞ → Ctx → Ctx
a ∷ᵢ (Γ , Φ) = (a ∷ Γ) , Φ

_∷ₗ_ : Type ∞ → Ctx → Ctx
a ∷ₗ (Γ , Φ) = Γ , a ∷ Φ

CtxTf = Ctx → Ctx

infixr 20 _◂_
_◂_ : Type ∞ → CtxTf → CtxTf
(a ◂ f) Δ with isEmp? a
... | yes (u , refl) = u ∷ᵢ f Δ
... | no  ¬u         = a ∷ₗ f Δ
