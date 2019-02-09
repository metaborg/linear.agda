module Sessions.Syntax.Expr where

open import Level
open import Size
open import Function

open import Data.Product
open import Data.List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Codata.Thunk

open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Sessions.Syntax.Types

open import Relation.Unary.Separation
open UnitalSep ⦃...⦄


data Exp : Type ∞ → LCtx → Set where

  var  : ∀[ Exactly a ⇒ Exp a ]

  -- value constructors
  unit : ∀[ Emp ⇒ Exp unit ]

  -- linear function introduction and elimination
  λₗ   : ∀ a → ∀[ a ◂ id ⊢ Exp b ⇒ Exp (a ⊸ b) ]
  _·_  :       ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]

  -- product introduction and elimination
  pair    : ∀[ Exp a ✴ Exp b ⇒ Exp (prod a b) ]
  letpair : ∀[ Exp (prod a b)  ✴ a ◂ b ◂ id ⊢ Exp c ⇒ Exp c ]

  -- io
  send : ∀ {b} → ∀[ Exp a ✴ Exp (chan (a ⅋ b)) ⇒ Exp (chan (b .force)) ]
  recv : ∀ {b} → ∀[ Exp (chan (a ⊗ b)) ⇒ Exp (prod a (chan (b .force))) ]

  -- link
  link : ∀[ chan α ◂ id ⊢ Exp (chan end!) ✴ chan (α ⁻¹) ◂ id ⊢ Exp b ⇒ Exp b ]

  -- termination
  terminate : ∀[ Exp (chan end?) ⇒ Exp unit ]
