module Sessions.Semantics.Commands where

open import Prelude
open import Data.Fin

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values

mutual
  data Cmd : Pred RCtx 0ℓ where
    send    : ∀ {a α}   → ∀[ (Endptr (a ! α) ✴ Val a) ⇒ Cmd ]
    receive : ∀ {a α}   → ∀[ Endptr (a ¿ α) ⇒ Cmd ]
    close   :             ∀[ Endptr end ⇒ Cmd ]
    fork    :             ∀[ Thread unit ⇒ Cmd ]

  δ : ∀ {Δ} → Cmd Δ → Pred RCtx 0ℓ
  δ (send {α = α} _)    = Endptr α
  δ (receive {a} {α} _) = Endptr α ✴ Val a 
  δ (close _)           = Emp
  δ (fork {α} _)        = Emp

  open import Relation.Unary.Separation.Monad.Free Cmd δ

  Thread : Type → Pred RCtx _
  Thread a = Free (Val a)
