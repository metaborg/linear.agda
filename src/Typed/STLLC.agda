open import Data.List
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_) public
open import Function

open import Relation.Unary.Separation 

module Typed.STLLC where

data Ty : Set where
  numt : Ty
  _⊸_ : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty



instance separation : RawSep Ctx
separation = record { _⊎_≣_ = Interleaving }

instance unital' : RawUnitalSep Ctx
unital' = record { ε = [] ; sep = separation }

open RawSep ⦃...⦄
open RawUnitalSep ⦃...⦄



infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(a ◂ f) Γ = a ∷ f Γ

Just : Ty → Pred Ctx _
Just t = Exactly (t ∷ ε)

data Expr : Ty → Ctx → Set where
  add :
    ∀[ Expr numt ✴ Expr numt ⇒ Expr numt ]
  num :
    ∀[ Emp ⇒ Expr numt ]
  ƛ_ : ∀ {a b} →
    ∀[ (a ◂ id ⊢ Expr b) ⇒ Expr (a ⊸ b) ]
  _∙_ : ∀ {a b} →
    ∀[ Expr (a ⊸ b) ✴ Expr a ⇒ Expr b ]
  var : ∀ {a} →
    ∀[ Just a ⇒ Expr a ]
