module Typed.LTLCRef where

open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Function
open import Category.Monad

open import Relation.Unary.Separation 
open import Relation.Unary.Separation.Construct.List as L
open import Relation.Unary.Separation.Env
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Reader
open import Relation.Unary.Separation.Monad.State

open import Prelude hiding (Lift; lookup)

data Ty : Set where
  nat  : Ty
  unit : Ty
  ref  : Ty → Ty
  _⊸_  : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Construct.Product

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

variable a b : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

data Exp : Ty → Ctx → Set where
  num   : ℕ → ε[ Exp nat ]
  lam   : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  ap    : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var   : ∀[ Just a ⇒ Exp a ]
  ref   : ∀[ Exp a ⇒ Exp (ref a) ]
  deref : ∀[ Exp (ref a) ⇒ Exp a ]
  asgn  : ∀[ Exp (ref a) ✴ Exp (a ⊸ b) ⇒ Exp (ref b) ]

-- store types
ST = List Ty

-- values
data Val : Ty → Pred ST 0ℓ where
  unit  :     ε[ Val unit ]
  num   : ℕ → ε[ Val nat  ]
  clos  : Exp b (a ∷ Γ) → ∀[ Allstar Val Γ ⇒ Val (a ⊸ b) ]
  ref   : ∀[ Just a ⇒ Val (ref a) ]

open Morphism (market ST)
open Monads (market ST)
open Reader (market ST) Val (State {V = Val})
  renaming (Reader to M)
open StateOps {V = Val} unit unit (λ where unit → refl)

do-update : ∀ {a b} → ∀[ Just a ✴ (Val a ─✴ⱼ M Γ₁ Γ₂ (Val b)) ⇒ⱼ M Γ₁ Γ₂ (Just b) ]
do-update (ptr ×⟨ σ ⟩ f) = do
  a ×⟨ σ₁ ⟩ f ← str _ (liftM (read ptr) ×⟨ j-map σ ⟩ inj f)
  b           ← app f a (⊎-comm σ₁)
  r ×⟨ σ ⟩ b  ← str (Val _) (liftM mkref ×⟨ ⊎-idˡ ⟩ inj b)
  liftM (write (r ×⟨ σ ⟩ b))

{-# TERMINATING #-}
mutual
  eval⊸ : ∀ {Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M Γ ε (Val b) ]
  eval⊸ e v = do
    clos e env ×⟨ σ₂ ⟩ v ← str (Val _) (eval e ×⟨ ⊎-idˡ ⟩ (inj v))
    empty                ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
    eval e

  eval : ∀ {Γ} → Exp a Γ → ε[ M Γ ε (Val a) ]

  eval (num n) = do
    return (num n)

  eval (var refl) = do
    (v :⟨ σ ⟩: nil) ← ask
    case ⊎-id⁻ʳ σ of λ where
      refl → return v

  eval (lam e) = do
    env ← ask
    return (clos e env)

  eval (ap (f ×⟨ Γ≺ ⟩ e)) = do
    v ← frame (⊎-comm Γ≺) (eval e)
    eval⊸ f v

  eval (ref e) = do
    v          ← eval e
    r ×⟨ σ ⟩ v ← str (Val _) (liftM mkref ×⟨ ⊎-idˡ ⟩ inj v)
    r ← liftM (write (r ×⟨ σ ⟩ v))
    return (ref r)

  eval (deref e) = do
    ref r ← eval e
    liftM (read r)

  eval (asgn (e₁ ×⟨ σ ⟩ e₂)) = do
    ref ra ← frame σ (eval e₁)
    rb ← do-update (ra ×⟨ ⊎-idʳ ⟩ (wandit (eval⊸ e₂)))
    return (ref rb)
