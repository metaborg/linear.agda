module Typed.LTLC where

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

open L.All


data Ty : Set where
  nat  : Ty
  _⊸_ : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

open RawSep ⦃...⦄
open RawUnitalSep ⦃...⦄

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

Just : Ty → Pred Ctx _
Just t = Exactly (t ∷ ε)

variable a b : Ty

data Exp : Ty → Ctx → Set where
  add : ∀[ Exp nat ✴ Exp nat ⇒ Exp nat ]
  num : ∀[ Emp ⇒ Exp nat ]
  lam : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  app : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var : ∀[ Just a ⇒ Exp a ]

mutual
  Env : Ctx → Set
  Env = All Val

  data Val : Ty → Set where
    num   : ℕ → Val nat
    clos  : ∀[ (a ◂ id ⊢ Exp b) ⇒ Env ] → Val (a ⊸ b)

  M : Set → Ctx → Set
  M A Γ = Env Γ → A

  eval : ∀[ Exp a ⇒ M (Val a) ]
  eval (add (e₁ ×⟨ σ ⟩ e₂)) env =
    let (envₗ , env₂) = all-split σ env
    in case eval e₁ envₗ of λ where
      (num n) → case eval e₂ env₂ of λ where
        (num m) → num (n + m)
  eval (num x) = {!!}
  eval (lam e) = {!!}
  eval (app f✴e) = {!!}
  eval (var x) = {!!}

-- module Arrowic where
  -- first : {P Q R : Pred Ctx 0ℓ} →
  --         ∀[ P ⇒ Q ] →
  --         ∀[ (P ✴ R) ⇒
  --            (Q ✴ R) ]
  -- first = {!!}

  -- _>>>_ : ∀ {P Q R : Pred Ctx 0ℓ} →
  --         ∀[ P ⇒ Q ] →
  --         ∀[ Q ⇒ R ] →
  --         ∀[ P ⇒ R ]
  -- x >>> y = {!!}

  -- mapM′ : ∀ {A B} →
  --         (A → B) →
  --         ∀[ M A ⇒ M B ]
  -- mapM′ = {!!}
