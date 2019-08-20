{-# OPTIONS --sized-types #-}
module Sessions.Syntax.Expr where

open import Prelude

open import Sessions.Syntax.Types

data Exp : Type ∞ → LCtx → Set where

  var       : ∀[ Just a ⇒ Exp a ]

  -- value constructors
  unit      : ∀[ Emp ⇒ Exp unit ]

  -- linear function introduction and elimination
  λₗ        : ∀ a → ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  app       :       ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]

  -- product introduction and elimination
  pairs     : ∀[ Exp a ✴ Exp b ⇒ Exp (prod a b) ]
  letpair   : ∀[ Exp (prod a b) ✴ (a ◂ b ◂ id ⊢ Exp c) ⇒ Exp c ]

  -- communication
  send      : ∀ {b} → ∀[ Exp a ✴ Exp (chan (a ! b)) ⇒ Exp (chan (b .force)) ]
  recv      : ∀ {b} → ∀[ Exp (chan (a ¿ b)) ⇒ Exp (prod (chan (b .force)) a) ]

  -- fork ; TODO unit
  fork      : ∀[ Exp (chan α ⊸ b) ⇒ Exp (chan (α ⁻¹)) ]

  -- termination
  terminate : ∀[ Exp (chan end) ⇒ Exp unit ]
