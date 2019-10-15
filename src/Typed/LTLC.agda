module Typed.LTLC where

open import Prelude
open import Function
open import Level
open import Category.Monad

open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Separation.Construct.Unit
open import Relation.Ternary.Separation.Allstar
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad.Reader

data Ty : Set where
  nat  : Ty
  _⊸_ : (a b : Ty) → Ty

open import Relation.Ternary.Separation.Construct.List Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

variable a b : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

data Exp : Ty → Ctx → Set where
  add : ∀[ Exp nat ✴ Exp nat ⇒ Exp nat ]
  num : ℕ → ε[ Exp nat ]
  lam : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  ap  : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var : ∀[ Just a ⇒ Exp a ]

module _ {{m : MonoidalSep 0ℓ}} where
  open MonoidalSep m using (Carrier)

  CPred : Set₁
  CPred = Carrier → Set

  mutual
    Env : Ctx → CPred
    Env = Allstar Val

    data Val : Ty → CPred where
      num   : ℕ → ε[ Val nat ]
      clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

  open ReaderMonad Val
  open Monads.Monad reader-monad
  open Monads using (str; _&_; typed-str)

  {-# TERMINATING #-}
  eval : Exp a Γ → ε[ Reader Γ ε (Val a) ]

  eval (num n) = do
    return (num n)

  eval (add (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    (num n₁) ← frame Γ≺ (eval e₁)
    (num n₂) ← eval e₂
    return (num (n₁ + n₂))

  eval (lam e) = do
    env ← ask
    return (clos e env)

  eval (ap (f ×⟨ Γ≺ ⟩ e)) = do
    v                   ← frame (⊎-comm Γ≺) (eval e)
    clos e env ×⟨ σ ⟩ v ← eval f & v
    empty               ← append (v :⟨ ⊎-comm σ ⟩: env)
    eval e

  eval (var refl) = do
    lookup
