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

open import Relation.Unary.Separation Ctx proj₁

data Var : Type ∞ → Ctx → Set where
  -- choose from the unrestricted context
  -- provided that the linear context is empty
  ivar : ∀[ Emp    ⇒ (u ∈ᵢ_)    ⇒ Var (li u) ] 
  -- pick the only element from the linear context
  lvar : ∀[ Only a              ⇒ Var a      ]

data Exp : Type ∞ → Ctx → Set where

  -- variables (linear and intuitionistic)
  var  : ∀[ Var a ⇒ Exp a ]

  -- value constructors
  unit : ∀[ Emp ⇒ Exp unit ]

  -- linear function introduction and elimination
  λₗ   : (a : Type ∞) → ∀[ a ◂ id ⊢ Exp b ⇒ Exp (a ⊸ b) ]
  _·_  :                ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]

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
