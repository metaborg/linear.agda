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

open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Construct.Product
open import Relation.Ternary.Separation.Construct.List

{- Unrestricted-, Session- and Expression types-}
module _ where
  mutual
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

  LCtx = List Type   -- linear contexts
  variable
    Γ Γ' Γ₁ Γ₂ Γ₃ Γ₄ : LCtx

{- Some conventions -}
variable
  a b c   : Type
  α β γ   : SType

{- Duality -}
module _ where

  infixl 1000 _⁻¹
  _⁻¹  : SType → SType 
  (a ! β) ⁻¹ = a ¿ β ⁻¹
  (a ¿ β) ⁻¹ = a ! β ⁻¹
  end ⁻¹     = end

  dual-end : ∀ {α} → α ⁻¹ ≡ end → α ≡ end
  dual-end {x ! α} ()
  dual-end {x ¿ α} ()
  dual-end {end} refl = refl

  dual-involutive : ∀ {α} → α ⁻¹ ⁻¹ ≡ α
  dual-involutive {x ! α} = cong (_!_ _) dual-involutive
  dual-involutive {x ¿ α} = cong (_¿_ _) dual-involutive
  dual-involutive {end} = refl
