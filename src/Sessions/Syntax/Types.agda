module Sessions.Syntax.Types where

open import Level
open import Function

open import Data.Bool
open import Data.List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Codata.Thunk as Thunk

open import Algebra
open import Algebra.FunctionProperties

open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as DecM
open import Relation.Nullary.Product
open import Relation.Binary.PropositionalEquality as P hiding ([_])

open import Relation.Unary.Separation
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.List

{- Unrestricted-, Session- and Expression types-}
module _ where
  mutual
    data UType : Set where
      unit  : UType  
      prod  : UType → UType →  UType

    -- crefnel types
    infixr 10 _¿_
    data SType : Set where
      _!_ _¿_ : Type → SType → SType
      end     : SType 

    data Type : Set where
      unit  : Type
      cref  : SType → Type
      prod  : Type → Type → Type
      _⊸_   : Type → Type → Type

{- Contexts -}
module _ where

  LCtx = List Type   -- linear
  SCtx = List SType  -- sessions

  variable
    Γ Γ' Γ₁ Γ₂ Γ₃ Γ₄ : LCtx

{- Separation of contexts -}
module _ {t} {T : Set t} where

  private
    Ctx : Set t
    Ctx = List T

  LPred : (p : Level) → Set (t ⊔ Level.suc p)
  LPred p = Ctx → Set p

{- Some conventions -}
variable
  u v w   : UType
  a b c   : Type
  α β γ   : SType

{- Duality -}
module _ where

  infixl 1000 _⁻¹
  _⁻¹  : SType → SType 
  (a ! β) ⁻¹ = a ¿ β ⁻¹
  (a ¿ β) ⁻¹ = a ! β ⁻¹
  end ⁻¹     = end

  dual-involutive : ∀ {α} → α ⁻¹ ⁻¹ ≡ α
  dual-involutive {x ! α} = cong (_!_ _) dual-involutive
  dual-involutive {x ¿ α} = cong (_¿_ _) dual-involutive
  dual-involutive {end} = refl

{- Subset of unrestricted types -}
module _ where

  li : UType → Type
  li unit = unit
  li (prod a b) = prod (li a) (li b)

  -- IsUnr : Type → Set
  -- IsUnr a = ∃ λ u → li u ≡ a

  -- isUnr? : Decidable IsUnr
  -- isUnr? unit = yes (unit , P.refl)
  -- isUnr? (cref x) = no λ where
  --   (unit , ())
  --   (prod _ _ , ())
  -- isUnr? (prod a₁ a₂) = DecM.map′
  --   (λ where ((u , P.refl) , (v , P.refl)) → prod u v , P.refl)
  --   (λ where
  --     (unit , ())
  --     (prod a b , P.refl) → (a , P.refl) , (b , P.refl))
  --       ((isUnr? a₁) ×-dec (isUnr? a₂))
  -- isUnr? (a₁ ⊸ a₂) = no λ where
  --   (unit , ())
  --   (prod _ _ , ())

  CtxTf = LCtx → LCtx

  infixr 20 _◂_
  _◂_ : Type → CtxTf → CtxTf
  (a ◂ f) Δ = a ∷ f Δ
