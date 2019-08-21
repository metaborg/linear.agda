module Typed.LTLCRef where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.List.All
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Function
open import Level
open import Category.Monad

open import Relation.Unary.Separation 
open import Relation.Unary.Separation.Construct.List as L

open L.LinearEnv

data Ty : Set where
  nat  : Ty
  unit : Ty
  ref  : Ty → Ty
  _⊸_  : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

open import Relation.Unary.Separation.Construct.Auth Ctx

open RawSep ⦃...⦄
open RawUnitalSep ⦃...⦄

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

Just : Ty → Pred Ctx _
Just t = Exactly (t ∷ ε)

variable a b : Ty

data Exp : Ty → Ctx → Set where
  num   : ∀[ Emp ⇒ Exp nat ]
  lam   : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  app   : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var   : ∀[ Just a ⇒ Exp a ]
  ref   : ∀[ Exp a ⇒ Exp (ref a) ]
  deref : ∀[ Exp (ref a) ⇒ Exp (ref a) ]
  del   : ∀[ Exp (ref a) ⇒ Exp unit ]

-- store types
ST = List Ty

mutual
  -- typed stores
  St = Allstar Val

  -- values
  data Val : Ty → Pred ST 0ℓ where
    unit  :     ε[ Val unit ]
    num   : ℕ → ε[ Val nat  ]
    clos  : ∀ {Γ} → Exp b Γ → ∀[ Env Val Γ ⇒ Val (a ⊸ b) ]
    ref   : ∀[ Just a ⇒ Val a ]

  M : ∀ {p} → Set → Pred Auth p → Pred Auth  p
  M Γ₁ Γ₂ P = (○ (Env Γ₁) ✴ St) ==✴ ○ (P ✴ Env Γ₂) ✴ St

  -- eval : ∀[ Exp a ⇒ M (Val a) ]
  -- eval (num x) = {!!}
  -- eval (lam e) = {!!}
  -- eval (app f✴e) = {!!}
  -- eval (var x) = {!!}
  -- eval (ref e) = {!!}
  -- eval (deref e) = {!!}
  -- eval (del e) = {!!}
