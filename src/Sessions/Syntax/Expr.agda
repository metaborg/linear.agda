module Sessions.Syntax.Expr where

open import Prelude

open import Sessions.Syntax.Types
open import Relation.Unary.Separation.Construct.List Type

data Exp : Type → LCtx → Set where

  var       : ∀[ Just a ⇒ Exp a ]

  -- value constructors
  unit      : ε[ Exp unit ]

  -- linear function introduction and elimination
  lam       : ∀ a → ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  ap        :       ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]

  -- product introduction and elimination
  pairs     : ∀[ Exp a ✴ Exp b ⇒ Exp (prod a b) ]
  letpair   : ∀[ Exp (prod a b) ✴ (a ◂ b ◂ id ⊢ Exp c) ⇒ Exp c ]

  -- communication
  send      : ∀ {b} → ∀[ Exp a ✴ Exp (cref (a ! b)) ⇒ Exp (cref b) ]
  recv      : ∀ {b} → ∀[ Exp (cref (a ¿ b)) ⇒ Exp (prod (cref b) a) ]

  -- fork ; TODO unit
  fork      : ∀[ Exp (unit ⊸ unit) ⇒ Exp unit ]

  -- termination
  terminate : ∀[ Exp (cref end) ⇒ Exp unit ]
