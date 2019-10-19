module Sessions.Semantics.Commands where

open import Prelude
open import Data.Fin

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values

mutual
  data Cmd : Pred RCtx 0ℓ where
    fork    :             ∀[ Thread unit ⇒ Cmd ]
    mkchan  : ∀ α       → ε[ Cmd ]
    send    : ∀ {a α}   → ∀[ (Endptr (a ! α) ✴ Val a) ⇒ Cmd ]
    receive : ∀ {a α}   → ∀[ Endptr (a ¿ α) ⇒ Cmd ]
    close   :             ∀[ Endptr end ⇒ Cmd ]

  δ : ∀ {Δ} → Cmd Δ → Pred RCtx 0ℓ
  δ (fork {α} _)        = Emp
  δ (mkchan α)          = Endptr α ✴ Endptr (α ⁻¹)
  δ (send {α = α} _)    = Endptr α
  δ (receive {a} {α} _) = Val a ✴ Endptr α
  δ (close _)           = Emp

  open import Relation.Ternary.Separation.Monad.Free Cmd δ renaming (Cont to Cont')
  open import Relation.Ternary.Separation.Monad.Error

  Thread : Type → Pred RCtx _
  Thread a = ExceptTrans.Except Free Error (Val a)
