module Sessions.Syntax.Values where

open import Prelude hiding (both)
open import Relation.Unary
open import Data.List.Properties using (++-isMonoid)
import Data.List as List

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Morphisms

data Runtype : Set where
  endp : SType → Runtype
  chan : SType → SType → Runtype
  
data SplitRuntype : Runtype → Runtype → Runtype → Set where
  lr : ∀ {a b} → SplitRuntype (endp a) (endp b) (chan a b)
  rl : ∀ {a b} → SplitRuntype (endp b) (endp a) (chan a b)

instance
  ≺-raw-sep : RawSep Runtype
  RawSep._⊎_≣_ ≺-raw-sep = SplitRuntype

  ≺-has-sep : IsSep ≺-raw-sep
  IsSep.⊎-comm ≺-has-sep lr = rl
  IsSep.⊎-comm ≺-has-sep rl = lr
  IsSep.⊎-assoc ≺-has-sep lr ()
  IsSep.⊎-assoc ≺-has-sep rl ()

RCtx = List Runtype

-- Almost a PRSA morphism; except that j-⊎ doesnt hold
module _ where

  open import Data.List.Relation.Ternary.Interleaving.Propositional as I
  open import Relation.Unary.Separation.Construct.ListOf Runtype
  import Relation.Unary.Separation.Construct.List as L

  endpoints = List.map endp

  from-interleaving : ∀ {xs ys zs : SCtx} → I.Interleaving xs ys zs → Split (endpoints xs) (endpoints ys) (endpoints zs)
  from-interleaving [] = []
  from-interleaving (consˡ σ) = to-left (from-interleaving σ)
  from-interleaving (consʳ σ) = to-right (from-interleaving σ)

  to-interleaving : ∀ {xs ys zs : SCtx} → Split (endpoints xs) (endpoints ys) (endpoints zs) → I.Interleaving xs ys zs
  to-interleaving {x₁ ∷ xs} {[]} {.x₁ ∷ zs}      (to-left σ) = consˡ (to-interleaving σ)
  to-interleaving {x₁ ∷ xs} {x₂ ∷ ys} {.x₁ ∷ zs} (to-left σ) = consˡ (to-interleaving σ)
  to-interleaving {x₁ ∷ xs} {x₂ ∷ ys} {.x₂ ∷ zs} (to-right σ) = consʳ (to-interleaving σ)
  to-interleaving {[]} {x₁ ∷ ys} {.x₁ ∷ zs}      (to-right σ) = consʳ (to-interleaving σ)
  to-interleaving {[]} {[]} {[]} [] = []

mutual
  Env = Allstar Val

  data Closure : Type → Type → Pred SCtx 0ℓ where
    clos : ∀ {a} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Closure a b ]

  data Val : Type → Pred SCtx 0ℓ where
    tt    : ε[ Val unit ]
    cref  : ∀[ Just α ⇒ Val (cref α)   ]
    pairs : ∀[ Val a ✴ Val b  ⇒ Val (prod a b) ]
    clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

open import Relation.Unary.Separation.Env public

data Client {p} (P : Pred SCtx p) : Pred RCtx p where
  client : ∀ {xs} → P xs → Client P (List.map endp xs)

Endptr : SType → Pred RCtx _
Endptr = Client ∘ Just

pattern point = client refl

CVal : Type → Pred RCtx _
CVal = Client ∘ Val

