module Sessions.Syntax.Values where

open import Prelude
open import Relation.Unary

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Data.List.Relation.Ternary.Interleaving
open import Relation.Unary.Separation.Construct.List

Chan : SType ∞ → Pred SCtx 0ℓ
Chan = Just

mutual
  Env = Allstar Val

  data Closure : Type ∞ → Type ∞ → Pred SCtx 0ℓ where
    clos : ∀ {a} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Closure a b ]

  data Val : Type ∞ → Pred SCtx 0ℓ where
    tt    : ε[                 Val unit       ]
    chan  : ∀[ Chan α        ⇒ Val (chan α)   ]
    pairs : ∀[ Val a ✴ Val b ⇒ Val (prod a b) ]
    clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

open import Relation.Unary.Separation.Env public
