module Sessions.Syntax.Values where

open import Prelude hiding (both)
open import Relation.Unary
open import Data.List.Properties using (++-isMonoid)
import Data.List as List

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Relation.Unary.Separation.Morphisms

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
open import Relation.Unary.Separation.Construct.ListOf Runtype public

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

-- -- Almost a PRSA morphism; except that j-⊎ doesnt hold
-- module _ where

--   open import Data.List.Relation.Ternary.Interleaving.Propositional as I
--   import Relation.Unary.Separation.Construct.List as L

--   endpoints = List.map endp

--   from-interleaving : ∀ {xs ys zs : SCtx} → I.Interleaving xs ys zs → Split (endpoints xs) (endpoints ys) (endpoints zs)
--   from-interleaving [] = []
--   from-interleaving (consˡ σ) = to-left (from-interleaving σ)
--   from-interleaving (consʳ σ) = to-right (from-interleaving σ)

--   to-interleaving : ∀ {xs ys zs : SCtx} → Split (endpoints xs) (endpoints ys) (endpoints zs) → I.Interleaving xs ys zs
--   to-interleaving {x₁ ∷ xs} {[]} {.x₁ ∷ zs}      (to-left σ) = consˡ (to-interleaving σ)
--   to-interleaving {x₁ ∷ xs} {x₂ ∷ ys} {.x₁ ∷ zs} (to-left σ) = consˡ (to-interleaving σ)
--   to-interleaving {x₁ ∷ xs} {x₂ ∷ ys} {.x₂ ∷ zs} (to-right σ) = consʳ (to-interleaving σ)
--   to-interleaving {[]} {x₁ ∷ ys} {.x₁ ∷ zs}      (to-right σ) = consʳ (to-interleaving σ)
--   to-interleaving {[]} {[]} {[]} [] = []
