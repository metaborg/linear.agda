module Sessions.Syntax.Values where

open import Prelude
open import Relation.Unary

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Data.List.Relation.Ternary.Interleaving

Chan : SType ∞ → Pred SCtx 0ℓ
Chan = Just

mutual
  data Closure : Type ∞ → Type ∞ → Pred SCtx 0ℓ where
    closure : ∀ {a} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Closure a b ]

  data Val : Type ∞ → Pred SCtx 0ℓ where
    tt    : ∀[ Emp           ⇒ Val unit       ]
    chan  : ∀[ Chan α        ⇒ Val (chan α)   ]
    pairs : ∀[ Val a ✴ Val b ⇒ Val (prod a b) ]
    clos  : ∀[ Closure a b   ⇒ Val (a ⊸ b) ]

  Env : List (Type ∞) → Pred SCtx 0ℓ
  Env = Allstar Val

