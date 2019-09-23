module Sessions.Semantics.Commands where

open import Prelude
open import Data.Fin
open import Sessions.Syntax.Types
open import Sessions.Syntax.Values

data Cmd : Pred SCtx 0ℓ where
  send    : ∀ {a α}   → ∀[ (Just (a ! α) ✴ Val a) ⇒ Cmd ]
  receive : ∀ {a α}   → ∀[ Just (a ¿ α) ⇒ Cmd ]
  close   :             ∀[ Just end ⇒ Cmd ]
  fork    : ∀ {α b}   → ∀[ Closure (chan α) b ⇒ Cmd ]

δ : ∀ {Δ} → Cmd Δ → Pred SCtx 0ℓ
δ (send {α = α} _)    = Just (α .force)
δ (receive {a} {α} _) = Just (α .force) ✴ Val a 
δ (close _)           = Emp
δ (fork {α} _)        = Just (α ⁻¹)
