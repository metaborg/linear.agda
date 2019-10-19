module Sessions.Semantics.Expr where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Monad.Reader

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr
-- open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime

open import Relation.Ternary.Separation.Construct.List Type
-- open import Relation.Ternary.Separation.Monad.Free Cmd δ
open import Relation.Ternary.Separation.Monad.Delay

module _ where

  mutual
    data Cmd : Pred RCtx 0ℓ where
      fork    :             ∀[ Thread unit ⇒ Cmd ]
      mkchan  : ∀ α       → ε[ Cmd ]
      send    : ∀ {a α}   → ∀[ (Endptr (a ! α) ✴ Val a) ⇒ Cmd ]
      receive : ∀ {a α}   → ∀[ Endptr (a ¿ α) ⇒ Cmd ]
      close   :             ∀[ Endptr end ⇒ Cmd ]
      yield   :             ε[ Cmd ]

    Cont : ∀ i {Δ} → Cmd Δ → Pt RCtx 0ℓ
    Cont i c P = δ c ─✴ Free i P

    data Free i : Pt RCtx 0ℓ where
      pure   : ∀ {P}   → ∀[ P ⇒ Free i P ]
      impure : ∀ {P Φ} → Thunk (λ j → (∃[ Cmd ]✴ (λ c → Cont j c P)) Φ) i → Free i P Φ

    δ : ∀ {Δ} → Cmd Δ → Pred RCtx 0ℓ
    δ (fork {α} _)        = Emp
    δ (mkchan α)          = Endptr α ✴ Endptr (α ⁻¹)
    δ (send {α = α} _)    = Endptr α
    δ (receive {a} {α} _) = Val a ✴ Endptr α
    δ (close _)           = Emp
    δ yield               = Emp

    Thread : Type → Pred RCtx _
    Thread a = Free ∞ (Val a)

  open Monads using (Monad; str; _&_) public

  m-monad : ∀ {i} → Monad ⊤ _ (λ _ _ → Free i)
  Monad.return m-monad px = pure px
  app (Monad.bind m-monad f) (pure px) σ = app f px σ
  app (Monad.bind m-monad f) (impure tx) σ =
    impure λ where
      .force →
        let
          cmd ×⟨ σ₁ ⟩ κ = tx .force
          _ , σ₂ , σ₃   = ⊎-assoc σ₁ (⊎-comm σ)
        in cmd ×⟨ σ₂ ⟩ wand λ r σ₄ →
          let _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₃) σ₄ in
          app (Monad.bind m-monad f) (app κ r τ₂) τ₁ 

  module _ {i} where
    open ReaderTransformer id-morph Val (Free i) {{m-monad}} renaming (Reader to T) public

  M : Size → LCtx → LCtx → Pt RCtx 0ℓ
  M i Γ₁ Γ₂ P = T {i} Γ₁ Γ₂ P

  -- open import Relation.Ternary.Separation.Monad.Free Cmd δ renaming (Cont to Cont')

  ⟪_⟫ : ∀ {i Φ} → (c : Cmd Φ) → Free i (δ c) Φ
  ⟪_⟫ c = 
    impure (λ where .force → c ×⟨ ⊎-idʳ ⟩ wand λ r σ → case ⊎-id⁻ˡ σ of λ where refl → pure r )

open Monad reader-monad public
mutual
  eval : ∀ {i} → Exp a Γ → ε[ M i Γ [] (Val a) ]

  eval unit = do
    return tt

  eval (var refl) = do
    (v :⟨ σ ⟩: nil) ← ask
    case ⊎-id⁻ʳ σ of λ where
      refl → return v

  eval (lam a e) = do
    env ← ask
    return (clos e env)

  eval (ap (f ×⟨ Γ≺ ⟩ e)) = do
    v ← frame (⊎-comm Γ≺) (►eval e)
    {!!} -- eval⊸ f v

  eval (pairs (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (►eval e₁)
    v₂⋆v₂ ← ►eval e₂ & v₁
    return (pairs (✴-swap v₂⋆v₂))

  eval (letpair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    pairs (v₁ ×⟨ σ ⟩ v₂) ← frame Γ≺ (►eval e₁)
    empty ← prepend (cons (v₁ ×⟨ σ ⟩ singleton v₂))
    ►eval e₂

  eval (send (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (►eval e₁)
    cref φ ×⟨ σ ⟩ v₁ ← ►eval e₂ & v₁
    φ' ← liftM  ⟪ send (φ ×⟨ σ ⟩ v₁) ⟫
    return (cref φ')

  eval (recv e) = do
    cref φ ← ►eval e
    v ×⟨ σ ⟩ φ' ← liftM  ⟪ receive φ ⟫
    return (pairs (cref φ' ×⟨ ⊎-comm σ ⟩ v))

  eval (fork e) = do 
    clos body env ← ►eval e
    empty ← liftM ⟪ fork (app (runReader (cons (tt ×⟨ ⊎-idˡ ⟩ env))) (►eval body) ⊎-idʳ) ⟫ -- (app (runReader (cons (tt ×⟨ ⊎-idˡ ⟩ env))) (►eval body) ⊎-idʳ)
    return tt

  eval (terminate e) = do
    cref φ ← ►eval e
    empty ← liftM ⟪ close φ ⟫
    return tt

  -- eval⊸ : ∀ {i Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M i Γ [] (Val b) ]
  -- eval⊸ e v = do
  --   (clos e env) ×⟨ σ₂ ⟩ v ← ►eval e & v
  --   empty                  ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
  --   ►eval e

  -- ►eval⊸ : ∀ {i Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M i Γ [] (Val b) ]
  -- app (►eval⊸ e v) E σ = impure λ where
  --   .force →
  --     yield
  --       ×⟨ ⊎-idˡ ⟩
  --     wand (λ where empty σ' → case ⊎-id⁻ʳ σ' of λ where refl → app (eval⊸ e v) E σ )

  ►eval : ∀ {i} → Exp a Γ → ε[ M i Γ [] (Val a) ]
  app (►eval e) E σ = impure λ where
    .force →
      yield
        ×⟨ ⊎-idˡ ⟩
      wand (λ where empty σ' → case ⊎-id⁻ʳ σ' of λ where refl → app (eval e) E σ )
