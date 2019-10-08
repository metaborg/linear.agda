module Sessions.Semantics.Commands where

open import Prelude
open import Data.Fin

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values

data Cmd : Pred RCtx 0ℓ where
  send    : ∀ {a α}   → ∀[ (Endptr (a ! α) ✴ Val a) ⇒ Cmd ]
  receive : ∀ {a α}   → ∀[ Endptr (a ¿ α) ⇒ Cmd ]
  close   :             ∀[ Endptr end ⇒ Cmd ]
  fork    : ∀ {α b}   → ∀[ Closure (cref α) b ⇒ Cmd ]

δ : ∀ {Δ} → Cmd Δ → Pred RCtx 0ℓ
δ (send {α = α} _)    = Endptr α
δ (receive {a} {α} _) = Endptr α ✴ Val a 
δ (close _)           = Emp
δ (fork {α} _)        = Endptr (α ⁻¹)
