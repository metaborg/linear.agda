module Typed.LTLCRef where

open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Function
open import Category.Monad

open import Relation.Ternary.Separation 
open import Relation.Ternary.Separation.Allstar
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Monad.Reader

open import Prelude

data Ty : Set where
  nat  : Ty
  unit : Ty
  ref  : Ty → Ty
  prod : Ty → Ty → Ty
  _⊸_  : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

open import Relation.Ternary.Separation.Construct.List Ty
open import Relation.Ternary.Separation.Construct.Market
open import Relation.Ternary.Separation.Construct.Product

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
  ap    : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var   : ∀[ Just a ⇒ Exp a ]
  ref   : ∀[ Exp a ⇒ Exp (ref a) ]
  deref : ∀[ Exp (ref a) ⇒ Exp a ]
  asgn  : ∀[ Exp (ref a) ✴ Exp (a ⊸ b) ⇒ Exp (ref b) ]
  pair  : ∀[ Exp a ✴ Exp b ⇒ Exp (prod a b) ]

-- store types
ST = List Ty

-- values
data Val : Ty → Pred ST 0ℓ where
  unit  :     ε[ Val unit ]
  num   : ℕ → ε[ Val nat  ]
  clos  : Exp b (a ∷ Γ) → ∀[ Allstar Val Γ ⇒ Val (a ⊸ b) ]
  ref   : ∀[ Just a ⇒ Val (ref a) ]
  pair  : ∀[ Val a ✴ Val b ⇒ Val (prod a b) ]

{- The 'give-it-to-me-straight' semantics -}

Store : ST → ST → Set
Store = Allstar Val

-- {- First attempt -- evaluation without a frame, seems simple enough... -}
-- eval₁ : ∀ {Ψ Γ} → Exp a Γ → Allstar Val Γ Φ₁ → Store Ψ Φ₂ → Φ₁ ⊎ Φ₂ ≣ Ψ →
--         ∃ λ Ψ' → ∃₂ λ Φ₃ Φ₄ → Store Ψ' Φ₃ × Val a Φ₄ × Φ₃ ⊎ Φ₄ ≣ Ψ'

-- eval₁ (num x) nil μ σ = -, -, -, μ , num x , ⊎-comm σ 

-- eval₁ (lam e) env μ σ = -, -, -, μ , (clos e env) , ⊎-comm σ

-- eval₁ (ap (f ×⟨ σ ⟩ e)) env μ σ₂ =
--   let
--     env₁ ×⟨ σ₃ ⟩ env₂ = repartition σ env
--     _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₃) σ₂

--   {- Oops, store contains more stuff than used; i.e. we have a frame -}
--   in case eval₁ f env₁ μ {!τ₂!} of λ where
--     (_ , _ , _ , μ' , clos e env₃ , σ₄) → {!!}

-- eval₁ (var x) = {!!}

-- eval₁ (ref e) = {!!}

-- eval₁ (deref e) = {!!}

-- eval₁ (asgn x) = {!!}

-- {- First attempt -- evaluation *with* a frame. Are you sure want this? -}
-- eval₂ : ∀ {Ψ Γ Φf} → Exp a Γ → Allstar Val Γ Φ₁ → Store Ψ Φ₂ → Φ₁ ⊎ Φ₂ ≣ Φ → Φ ⊎ Φf ≣ Ψ →
--         ∃₂ λ Φ' Ψ' → ∃₂ λ Φ₃ Φ₄ → Store Ψ' Φ₃ × Val a Φ₄ × Φ₃ ⊎ Φ₄ ≣ Φ' × Φ' ⊎ Φf ≣ Ψ'
-- eval₂ (num x) nil μ σ₁ σ₂ =
--   case ⊎-id⁻ˡ σ₁ of λ where refl → -, -, -, -, μ , num x , ⊎-idʳ , σ₂  
-- eval₂ (lam x) env μ σ₁ σ₂ = {!!}

-- eval₂ (pair (e₁ ×⟨ σ ⟩ e₂)) env μ σ₁ σ₂ =
--   let
--     env₁ ×⟨ σ₃ ⟩ env₂ = repartition σ env
--     _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₃) σ₁ -- separation between sub-env and store
--     _ , τ₃ , τ₄ = ⊎-assoc (⊎-comm τ₁) σ₂ -- compute the frame

--   in case eval₂ e₁ env₁ μ τ₂ τ₃ of λ where
--     (_ , _ , _ , _ , μ' , v₁ , σ₄ , σ₅) →
--        let v = eval₂ e₂ env₂ μ' {!τ₁!} {!!} in {!!}

-- eval₂ (var x) env μ σ₁ σ₂ = {!!}
-- eval₂ (ref e) env μ σ₁ σ₂ = {!!}
-- eval₂ (deref e) env μ σ₁ σ₂ = {!!}
-- eval₂ (asgn x) env μ σ₁ σ₂ = {!!}
-- eval₂ (ap (f ×⟨ σ ⟩ e)) env μ σ₁ σ₂ = {!!}

{- The monadic semantics -}

open import Relation.Ternary.Separation.Monad.State.Heap Val hiding (_⇒ⱼ_; _─✴ⱼ_; liftM)
open ReaderTransformer market Val (State Cells)
  renaming (Reader to M)
open Monads.Monad reader-monad
open Monads using (_&_; str; typed-str)

do-update : ∀ {a b} → ∀[ Just a ✴ (Val a ─✴ⱼ M Γ₁ Γ₂ (Val b)) ⇒ⱼ M Γ₁ Γ₂ (Just b) ]
do-update (ptr ×⟨ σ ⟩ f) = do
  a ×⟨ σ₁ ⟩ f ← liftM (read ptr) &⟨ demand σ ⟩ f
  b           ← app f a (⊎-comm σ₁)
  liftM (mkref b)

{-# TERMINATING #-}
mutual
  eval⊸ : ∀ {Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M Γ ε (Val b) ]
  eval⊸ e v = do
    clos e env ×⟨ σ₂ ⟩ v ← eval e & v
    empty                ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
    eval e

  eval : ∀ {Γ} → Exp a Γ → ε[ M Γ ε (Val a) ]

  eval (num n) = do
    return (num n)

  eval (var refl) = do
    (v :⟨ σ ⟩: nil) ← ask
    case ⊎-id⁻ʳ σ of λ where
      refl → return v

  eval (lam e) = do
    env ← ask
    return (clos e env)

  eval (pair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁    ← frame Γ≺ (eval e₁)
    v₂✴v₁ ← eval e₂ & v₁
    return (pair (✴-swap v₂✴v₁))

  eval (ap (f ×⟨ Γ≺ ⟩ e)) = do
    v ← frame (⊎-comm Γ≺) (eval e)
    eval⊸ f v

  eval (ref e) = do
    v ← eval e
    r ← liftM (mkref v)
    return (ref r)

  eval (deref e) = do
    ref r ← eval e
    liftM (read r)

  eval (asgn (e₁ ×⟨ σ ⟩ e₂)) = do
    ref ra ← frame σ (eval e₁)
    rb ← do-update (ra ×⟨ ⊎-idʳ ⟩ (wandit (eval⊸ e₂)))
    return (ref rb)
