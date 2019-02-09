module Sessions.Syntax.Runtime where

open import Size
open import Level
open import Data.Product
open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality as P
open import Data.List
open import Codata.Thunk

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open UnitalSep ⦃...⦄

data Val : Type ∞ → Pred SCtx 0ℓ where
  tt   : ∀[ Emp           ⇒ Val unit       ]
  chan : ∀[ Just α        ⇒ Val (chan α)   ]
  pair : ∀[ Val a ✴ Val b ⇒ Val (prod a b) ]

data Env : List (Type ∞) → Pred SCtx 0ℓ where
  []  :          ∀[ Emp            ⇒ Env []       ]
  _∷_ : ∀ {as} → ∀[ Val a ✴ Env as ⇒ Env (a ∷ as) ]

-- writing to a queue is fast and pushes to the queue.
-- reading is slow.
data Queue (i : Size) : SType ∞ → SType ∞ → Pred SCtx 0ℓ where
  empty : ∀[ Emp ⇒ Queue i α α ] 
  cons  : ∀ {α} →
          ∀[ Val a
             ✴ (λ Δ → Thunk[ j < i ] (Queue j (a ⅋ α) β Δ))
             ⇒ Queue i (α .force) β ]

data Buffer : Pred (SCtx × SCtx) 0ℓ where
  atₗ : ∀[ (Queue ∞ α β ⟨×⟩ Exactly (β    ∷ α ⁻¹ ∷ [])) ⇒ Buffer ]
  atᵣ : ∀[ (Queue ∞ α β ⟨×⟩ Exactly (α ⁻¹ ∷ β    ∷ [])) ⇒ Buffer ]

data Thread : Pred SCtx 0ℓ where
  ⟨_,_⟩ : ∀ {a Δ} → Exp a Δ → ∀[ Env Δ ⇒ Thread ]

module QueueExamples where
  private
    -- empty queue
    ex₁ : Queue _ α α ε
    ex₁ = empty P.refl

    unit►unit► : Thunk SType ⊆ SType
    unit►unit► α = unit ⅋ (λ where .force → unit ⅋ α)

    -- 1 element queue
    -- unit at ( unit ⅋ unit ⅋ α ) : Queue (unit ⅋ α) (unit ⅋ unit ⅋ α)
    ex₂ : ∀ {α} → Queue ∞ (unit ⅋ α) (unit►unit► α) ε
    ex₂ =
        cons (tt P.refl IsSep.×⟨ ⊎-identityˡ P.refl ⟩ λ where
          .force → ex₁)

    -- 2 element queue
    -- unit ∷ unit at ( unit ⅋ unit ⅋ α ) : Queue (unit ⅋ α) (unit ⅋ unit ⅋ α)
    ex₃ : ∀ {α} → Queue ∞ (α .force) (unit►unit► α) ε
    ex₃ {β} =
        cons (tt P.refl IsSep.×⟨ ⊎-identityˡ P.refl ⟩ λ where
          .force → ex₂ {β})

  private
    -- ε at α   ↭   unit ∷ unit at (unit ⅋ unit ⅋ α)
    buf₁ : ∀ {α} → Buffer (ε , (α .force) ⁻¹ ∷ unit►unit► α ∷ [] )
    buf₁ {α} = atᵣ (ex₃ {α} , P.refl)
