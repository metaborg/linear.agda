module Typed.LTLCRef where

open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Function
open import Category.Monad

open import Relation.Ternary.Separation 
open import Relation.Ternary.Separation.Allstar
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Monad.Reader

open import Prelude

data Ty : Set where
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

variable a b c : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

data Exp : Ty → Ctx → Set where
  -- base type
  tt       : ε[ Exp unit ]
  letunit  : ∀[ Exp unit ✴ Exp a ⇒ Exp a ]

  -- linear λ calculus
  var      : ∀[ Just a ⇒ Exp a ]
  lam      : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  ap       : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]

  -- products
  pair    : ∀[ Exp a ✴ Exp b ⇒ Exp (prod a b) ]
  letpair : ∀[ Exp (prod a b) ✴ (λ Γ → a ∷ b ∷ Γ) ⊢ Exp c ⇒ Exp c ]

  -- state
  ref     : ε[ Exp a ⇒ Exp (ref a) ]
  swaps   : ∀[ Exp (ref a) ✴ Exp b ⇒ Exp (prod a (ref b)) ]
  del     : ε[ Exp (ref unit) ⇒ Exp unit ]

-- store types
ST = List Ty

-- values
data Val : Ty → Pred ST 0ℓ where
  tt    : ε[ Val unit ]
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

module _ {i : Size} where
  open import Relation.Ternary.Separation.Monad.Delay public
  open import Relation.Ternary.Separation.Monad.State
  open import Relation.Ternary.Separation.Monad.State.Heap Val

  open HeapOps (Delay i) {{ monad = delay-monad }}
    using (state-monad; newref; read; write; Cells)
    public

  open ReaderTransformer id-morph Val (StateT (Delay i) Cells)
    {{ monad = state-monad }}
    renaming (Reader to M'; reader-monad to monad)
    public

  open Monads.Monad monad public
  open Monads using (_&_; str; typed-str) public

M : Size → (Γ₁ Γ₂ : Ctx) → Pt ST 0ℓ
M i = M' {i}

mutual
  eval⊸ : ∀ {i Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ M i Γ ε (Val b) ]
  eval⊸ e v = do
    clos e env ×⟨ σ₂ ⟩ v ← ►eval e & v
    empty                ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
    ►eval e

  eval : ∀ {i Γ} → Exp a Γ → ε[ M i Γ ε (Val a) ]

  eval tt = do
    return tt

  eval (letunit (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    tt ← frame Γ≺ (►eval e₁)
    ►eval e₂

  eval (var refl) = do
    lookup

  eval (lam e) = do
    env ← ask
    return (clos e env)

  eval (pair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁    ← frame Γ≺ (►eval e₁)
    v₂✴v₁ ← ►eval e₂ & v₁
    return (pair (✴-swap v₂✴v₁))

  eval (letpair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    pair (v₁ ×⟨ σ ⟩ v₂) ← frame Γ≺ (►eval e₁)
    empty               ← prepend (cons (v₁ ×⟨ σ ⟩ (singleton v₂)))
    ►eval e₂

  eval (ap (f ×⟨ Γ≺ ⟩ e)) = do
    v ← frame (⊎-comm Γ≺) (►eval e)
    eval⊸ f v

  eval (ref e) = do
    v ← ►eval e
    r ← liftM (newref v)
    return (ref r)

  eval (swaps (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    ref ra ← frame Γ≺ (►eval e₁)
    vb ×⟨ σ₁ ⟩ ra ← ►eval e₂ & ra
    rb ×⟨ σ₂ ⟩ va ← liftM (write (ra ×⟨ ⊎-comm σ₁ ⟩ vb))
    return (pair (va ×⟨ (⊎-comm σ₂) ⟩ (ref rb)))

  eval (del e) = do
    ref r ← ►eval e
    liftM (read r) 

  ►eval : ∀ {i Γ} → Exp a Γ → ε[ M i Γ ε (Val a) ]
  app (app (►eval e) env σ) μ σ' = later (λ where .force → app (app (eval e) env σ) μ σ')
