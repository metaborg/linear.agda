module Sessions.Syntax.Values where

open import Prelude hiding (both)
open import Relation.Unary
open import Data.List.Properties using (++-isMonoid)

open import Sessions.Syntax.Types
open import Sessions.Syntax.Expr

open import Relation.Unary.Separation.Construct.List public

-- data Endpoint : Set where
--   _ʳ _ˡ both : SType ∞ → Endpoint

-- type : Endpoint → SType ∞
-- type (α ʳ) = α
-- type (α ˡ) = α
-- type (both α) = α
  
-- -- non-empty splits of endpoints
-- data _≺[_,_] : (x y z : Endpoint) → Set where
--   lr : (both α) ≺[ α ˡ , α ʳ ]
--   rl : (both α) ≺[ α ʳ , α ˡ ]
  
-- instance
--   ≺-raw-sep : RawSep Endpoint
--   RawSep._⊎_≣_ ≺-raw-sep = λ l r s → s ≺[ l , r ]

--   ≺-has-sep : IsSep ≺-raw-sep
--   IsSep.⊎-comm ≺-has-sep lr = rl
--   IsSep.⊎-comm ≺-has-sep rl = lr
--   IsSep.⊎-assoc ≺-has-sep lr ()
--   IsSep.⊎-assoc ≺-has-sep rl ()

-- Endpoints = List Endpoint

-- data Split : (Φ₁ Φ₂ Φ : Endpoints) → Set where
--   divide   : ∀ {x y z xs ys zs} → z ≺[ x , y ] → Split xs ys zs → Split (x ∷ xs) (y ∷ ys) (z ∷ zs)
--   to-left  : ∀ {z xs ys zs} → Split xs ys zs → Split (z ∷ xs) ys (z ∷ zs)
--   to-right : ∀ {z xs ys zs} → Split xs ys zs → Split xs (z ∷ ys) (z ∷ zs)
--   []       : Split [] [] []

-- -- Split yields a separation algebra
-- instance
--   splits : RawSep Endpoints
--   RawSep._⊎_≣_ splits = Split

--   split-is-sep : IsSep splits

--   -- commutes
--   IsSep.⊎-comm split-is-sep (divide τ σ) = divide (⊎-comm τ) (⊎-comm σ)
--   IsSep.⊎-comm split-is-sep (to-left σ)  = to-right (⊎-comm σ)
--   IsSep.⊎-comm split-is-sep (to-right σ) = to-left (⊎-comm σ)
--   IsSep.⊎-comm split-is-sep [] = []
  
--   -- reassociates
--   IsSep.⊎-assoc split-is-sep σ₁ (to-right σ₂) with ⊎-assoc σ₁ σ₂
--   ... | _ , σ₄ , σ₅ = -, to-right σ₄ , to-right σ₅
--   IsSep.⊎-assoc split-is-sep (to-left σ₁) (divide τ σ₂) with ⊎-assoc σ₁ σ₂
--   ... | _ , σ₄ , σ₅ = -, divide τ σ₄ , to-right σ₅
--   IsSep.⊎-assoc split-is-sep (to-right σ₁) (divide τ σ₂)  with ⊎-assoc σ₁ σ₂
--   ... | _ , σ₄ , σ₅ = -, to-right σ₄ , divide τ σ₅
--   IsSep.⊎-assoc split-is-sep (divide τ σ₁) (to-left σ) with ⊎-assoc σ₁ σ
--   ... | _ , σ₄ , σ₅ = -, divide τ σ₄ , to-left σ₅
--   IsSep.⊎-assoc split-is-sep (to-left σ₁) (to-left σ)  with ⊎-assoc σ₁ σ
--   ... | _ , σ₄ , σ₅ = -, to-left σ₄ , σ₅
--   IsSep.⊎-assoc split-is-sep (to-right σ₁) (to-left σ) with ⊎-assoc σ₁ σ
--   ... | _ , σ₄ , σ₅ = -, to-right σ₄ , to-left σ₅
--   IsSep.⊎-assoc split-is-sep [] [] = -, [] , []
--   IsSep.⊎-assoc split-is-sep (divide lr _) (divide () _)
  
--   split-is-unital : IsUnitalSep splits []
--   IsUnitalSep.⊎-idˡ split-is-unital {[]}                           = []
--   IsUnitalSep.⊎-idˡ split-is-unital {x ∷ Φ}                        = to-right ⊎-idˡ
--   IsUnitalSep.⊎-id⁻ˡ split-is-unital (to-right σ) rewrite ⊎-id⁻ˡ σ = refl
--   IsUnitalSep.⊎-id⁻ˡ split-is-unital []                            = refl
  
--   split-has-concat : IsConcattative splits
--   IsConcattative._∙_ split-has-concat = _++_
--   IsConcattative.⊎-∙ₗ split-has-concat {Φₑ = []} σ = σ
--   IsConcattative.⊎-∙ₗ split-has-concat {Φₑ = x ∷ Φₑ} σ = to-left (⊎-∙ₗ σ) 
  
--   split-monoidal : MonoidalSep _
--   split-monoidal = record { monoid = ++-isMonoid }

-- data Chan : SType ∞ → Pred Endpoints 0ℓ where
--   endₗ : Chan α [ α ˡ ]
--   endᵣ : Chan α [ α ʳ ]

mutual
  Env = Allstar Val

  data Closure : Type → Type → Pred SCtx 0ℓ where
    clos : ∀ {a} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Closure a b ]

  data Val : Type → Pred SCtx 0ℓ where
    tt    : ε[ Val unit ]
    chan  : ∀[ Just α ⇒ Val (chan α)   ]
    pairs : ∀[ Val a ✴ Val b  ⇒ Val (prod a b) ]
    clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

open import Relation.Unary.Separation.Env public
