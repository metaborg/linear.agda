open import Data.List
open import Data.List.All
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_) public
open import Function
open import Level
open import Category.Monad

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
(x ◂ f) Γ = x ∷ f Γ

Just : Ty → Pred Ctx _
Just t = Exactly (t ∷ ε)

variable a b : Ty

data Expr : Ty → Ctx → Set where
  add :
    ∀[ Expr numt ✴ Expr numt ⇒ Expr numt ]
  num :
    ∀[ Emp ⇒ Expr numt ]
  ƛ_ : 
    ∀[ (a ◂ id ⊢ Expr b) ⇒ Expr (a ⊸ b) ]
  _∙_ :
    ∀[ Expr (a ⊸ b) ✴ Expr a ⇒ Expr b ]
  var :
    ∀[ Just a ⇒ Expr a ]

mutual
  Env : Ctx → Set
  Env = All Val

  data Val : Ty → Set where
    num   : Val numt
    clos  : 
      ∀[ (a ◂ id ⊢ Expr b) ⇒ Env ] → Val (a ⊸ b)

  M : Set → Ctx → Set
  M A Γ = Env Γ → A

  first : {P Q R : Pred Ctx 0ℓ} →
          ∀[ P ⇒ Q ] →
          ∀[ (P ✴ R) ⇒
             (Q ✴ R) ]
  first = {!!}

  _>>>_ : ∀ {P Q R : Pred Ctx 0ℓ} →
          ∀[ P ⇒ Q ] →
          ∀[ Q ⇒ R ] →
          ∀[ P ⇒ R ]
  x >>> y = {!!}

  mapM′ : ∀ {A B} →
          (A → B) →
          ∀[ M A ⇒ M B ]
  mapM′ = {!!}

  eval : ∀[ Expr a ⇒ M (Val a) ]
  eval (add (px RawSep.×⟨ sep₁ ⟩ qx)) = ?
  eval (num x) = {!!}
  eval (ƛ x) = {!!}
  eval (_∙_ x) = {!!}
  eval (var x) = {!!}
