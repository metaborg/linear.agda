module Typed.LTLCRef where

open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Function
open import Category.Monad

open import Relation.Unary.Separation 
open import Relation.Unary.Separation.Construct.List as L
open import Relation.Unary.Separation.Env
open import Relation.Unary.Separation.Monad

open import Prelude hiding (Lift; lookup)

data Ty : Set where
  nat  : Ty
  unit : Ty
  ref  : Ty → Ty
  _⊸_  : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

open import Relation.Unary.Separation.Construct.Auth
open import Relation.Unary.Separation.Construct.Product

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

variable a b : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

data Exp : Ty → Ctx → Set where
  num   : ℕ → ε[ Exp nat ]
  lam   : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  app   : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var   : ∀[ Just a ⇒ Exp a ]
  ref   : ∀[ Exp a ⇒ Exp (ref a) ]
  deref : ∀[ Exp (ref a) ⇒ Exp a ]
  asgn  : ∀[ Exp (ref a) ✴ Exp (a ⊸ b) ⇒ Exp (ref b) ]

-- store types
ST = List Ty

-- values
data Val : Ty → Pred ST 0ℓ where
  unit  :     ε[ Val unit ]
  num   : ℕ → ε[ Val nat  ]
  clos  : Exp b (a ∷ Γ) → ∀[ Allstar Val Γ ⇒ Val (a ⊸ b) ]
  ref   : ∀[ Just a ⇒ Val (ref a) ]

AP : (ℓ : Level) → Set (sucℓ ℓ)
AP ℓ = Pred (Auth Ctx) ℓ

M : ∀ {p} → Ctx → Ctx → Pred Ctx p → AP p
M Γ₁ Γ₂ P =
  (○ (Allstar Val Γ₁)) ─✴
  St ==✴
  (○ P) ✴ (○ (Allstar Val Γ₂)) ✴ St

instance
  M-monad : Monad {ℓ = 0ℓ} M
  Monad.return M-monad px env σ₂ st σ₃ =
    let _ , σ₄ , σ₅ = ⊎-assoc σ₂ σ₃
    in  ⤇-return (frag px ×⟨ σ₄ ⟩ env ×⟨ σ₅ ⟩ st) ⊎-idˡ
  Monad.bind M-monad = {!!}

ask : ε[ M Γ ε (Allstar Val Γ) ]
ask env σ = return {!!} {!!} {!!} -- nil ×⟨ σ ⟩ env

frame : ∀ {p} {P : Pred Ctx p} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ M Γ₁ ε P ⇒ M Γ₂ Γ₃ P ]
frame = {!!}

append : ∀[ Allstar Val Γ₁ ⇒[ ◌ ] M Γ₂ (Γ₂ ∙ Γ₁) Emp ]
append = {!!}

store : ∀[ Val a ⇒[ ◌ ] M Γ Γ (Just a) ]
store = {!!}

-- lookup : ε[ St ─✴ ○ (Just a) ==✴ ○ (Val a) ✴ St ]
-- lookup (lift st σ₀) (on-right σ₁) (frag refl) (on-left σ₂) with ⊎-id⁻ˡ σ₁

-- lookup (lift (cons (c ×⟨ σ ⟩ st)) (consˡ σ₀)) _ (frag refl) (on-left σ₂) | refl = {!st!}
-- lookup (lift st (consʳ σ₀)) _ (frag refl) (on-left σ₂) | refl = {!σ!}

-- -- store traversal
-- -- st-lookup (lift (cons (v ×⟨ σ ⟩ st)) (consˡ σ₀)) (on-right _) (frag refl) (on-left (consˡ σ₂)) | refl = λ φ → {!!} , {!!} , {!!} , frag {!v!} ×⟨ {!!} ⟩ {!!}
-- -- st-lookup (lift st (consʳ σ₀)) (on-right _) (frag refl) (on-left (consˡ σ₂)) | refl = {!!}

do-deref : ∀ {Γ} → ∀[ Just a ⇒[ ◌ ] M Γ Γ (Val a) ]
do-deref ptr σ₀ env σ₁ st σ₂ = {!!}

do-update : ∀[ Val a ⇒[ ◌ ] M Γ₁ Γ₂ (Val b) ] → ∀[ Just a ⇒[ ◌ ] M Γ₁ Γ₂ (Just b) ]
do-update = {!!}

--   -- let
--   --   _ , ρ₀ , ρ₁ = ⊎-assoc (⊎-comm σ₀) σ₁
--   --   _ , ρ₂ , ρ₃ = ⊎-assoc ρ₀ σ₂
--   -- in
--   -- ⤇-bind
--   --   (λ where (v ×⟨ σ₃ ⟩ st) σ₄ → ⤇-return (v ×⟨ {!!} ⟩ env ×⟨ {!!} ⟩ st) ⊎-idˡ)
--   --   ⊎-idˡ
--   --   (st-lookup st ⊎-idˡ ptr {!!}) {!!}

-- {-# TERMINATING #-}
-- mutual
--   eval⊸ : ∀ {Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒[ ◌ ] M Γ ε (Val b) ]
--   eval⊸ e v = do
--     clos e env ×⟨ σ₂ ⟩ v ← str (Val _) (eval e ×⟨ ⊎-idˡ ⟩ (frag v))
--     empty                ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
--     eval e

--   eval : ∀ {Γ} → Exp a Γ → ε[ M Γ ε (Val a) ]

--   eval (num n) = do
--     return (num n)

--   eval (var refl) = do
--     (v :⟨ σ ⟩: nil) ← ask
--     case ⊎-id⁻ʳ σ of λ where
--       refl → return v

--   eval (lam e) = do
--     env ← ask
--     return (clos e env)

--   eval (app (f ×⟨ Γ≺ ⟩ e)) = do
--     v ← frame (⊎-comm Γ≺) (eval e)
--     eval⊸ f v

--   eval (ref e) = do
--     v ← eval e
--     r ← store v
--     return (ref r)

--   eval (deref e) = do
--     ref r ← eval e
--     do-deref r

--   eval (asgn (e₁ ×⟨ σ ⟩ e₂)) = do
--     ref ra ← frame σ (eval e₁)
--     rb     ← do-update (eval⊸ e₂) ra
--     return (ref rb)
