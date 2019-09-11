module Typed.LTLC where

open import Prelude
open import Function
open import Level
open import Category.Monad

open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Unit
open import Relation.Unary.Separation.Env
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Reader

data Ty : Set where
  nat  : Ty
  _⊸_ : (a b : Ty) → Ty

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
  app : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
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

  open Reader Val

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

  eval (app (f ×⟨ Γ≺ ⟩ e)) = do
    v                   ← frame (⊎-comm Γ≺) (eval e)
    clos e env ×⟨ σ ⟩ v ← str _ (eval f ×⟨ ⊎-idˡ ⟩ inj v)
    empty ×⟨ σ ⟩ env    ← str (Allstar _ _) (append (singleton v) ×⟨ ⊎-comm σ ⟩ inj env)
    case (⊎-id⁻ˡ σ) of λ where
      refl → do
        empty ← append env
        eval e

  eval (var refl) = do
    cons (v ×⟨ σ ⟩ nil) ← ask
    case (⊎-id⁻ʳ σ) of λ where
      refl → return v
