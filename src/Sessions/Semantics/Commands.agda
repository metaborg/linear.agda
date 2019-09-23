module Sessions.Semantics.Commands where

open import Prelude
open import Data.Fin
open import Sessions.Syntax.Types
open import Sessions.Syntax.Values

data Cmd : Pred Endpoints 0ℓ where
  send    : ∀ {a α}   → ∀[ (Chan (a ! α) ✴ Val a) ⇒ Cmd ]
  receive : ∀ {a α}   → ∀[ Chan (a ¿ α) ⇒ Cmd ]
  close   :             ∀[ Chan end ⇒ Cmd ]
  fork    : ∀ {α b}   → ∀[ Closure (chan α) b ⇒ Cmd ]

δ : ∀ {Δ} → Cmd Δ → Pred Endpoints 0ℓ
δ (send {α = α} _)    = Chan (α .force)
δ (receive {a} {α} _) = Chan (α .force) ✴ Val a 
δ (close _)           = Emp
δ (fork {α} _)        = Chan (α ⁻¹)
