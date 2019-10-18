module Sessions.Syntax.Values where

open import Prelude hiding (both)
open import Relation.Unary
open import Data.Maybe
open import Data.List.Properties using (++-isMonoid)
import Data.List as List

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Relation.Ternary.Separation.Morphisms

data Runtype : Set where
  endp : SType → Runtype
  chan : SType → SType → Runtype

flipped : Runtype → Runtype
flipped (endp x)   = endp x
flipped (chan α β) = chan β α
  
data Ends : Runtype → Runtype → Runtype → Set where
  lr : ∀ {a b} → Ends (endp a) (endp b) (chan a b)
  rl : ∀ {a b} → Ends (endp b) (endp a) (chan a b)

instance
  ≺-raw-sep : RawSep Runtype
  RawSep._⊎_≣_ ≺-raw-sep = Ends

  ≺-has-sep : IsSep ≺-raw-sep
  IsSep.⊎-comm ≺-has-sep lr = rl
  IsSep.⊎-comm ≺-has-sep rl = lr
  IsSep.⊎-assoc ≺-has-sep lr ()
  IsSep.⊎-assoc ≺-has-sep rl ()

RCtx = List Runtype
open import Relation.Ternary.Separation.Construct.ListOf Runtype public

End : SType → Runtype → Set
End α τ = [ endp α ] ≤ [ τ ]

ending : ∀ {ys} → Ends (endp γ) ys (chan α β) → End γ (chan α β)
ending lr = -, divide lr ⊎-idˡ
ending rl = -, divide rl ⊎-idˡ

mutual
  Env = Allstar Val

  data Closure : Type → Type → Pred RCtx 0ℓ where
    clos : ∀ {a} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Closure a b ]

  Endptr = Just ∘ endp

  data Val : Type → Pred RCtx 0ℓ where
    tt    : ε[ Val unit ]
    cref  : ∀[ Endptr α ⇒ Val (cref α)   ]
    pairs : ∀[ Val a ✴ Val b  ⇒ Val (prod a b) ]
    clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]
