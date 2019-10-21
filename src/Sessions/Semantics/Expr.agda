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
open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime

open import Relation.Ternary.Separation.Construct.List Type
open import Relation.Ternary.Separation.Monad.Free Cmd δ 
  hiding (⟪_⟫)
open import Relation.Ternary.Separation.Monad.Error

open ErrorTrans Free {{monad = free-monad}} public
open ReaderTransformer id-morph Val (ErrorT Free) {{error-monad}}
  renaming (Reader to M)
open Monads using (Monad; str; _&_)
open Monad reader-monad

mutual
  eval⊸ : ∀ {Γ} → ℕ → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M Γ [] (Val b) ]
  eval⊸ n e v = do
    (clos e env) ×⟨ σ₂ ⟩ v ← ►eval n e & v
    empty                  ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
    ►eval n e

  ►eval : ℕ → Exp a Γ → ε[ M Γ [] (Val a) ]
  app (►eval zero    e) _ _ = partial (pure (inj₁ err))
  ►eval (suc n) e = eval n e 

  ⟪_⟫ : ∀ {Γ Φ} → (c : Cmd Φ) → M Γ Γ (δ c) Φ
  app (⟪_⟫ c) (inj E) σ = 
    partial (impure (c ×⟨ σ ⟩ 
      wand λ r σ' → pure (inj₂ (r ×⟨ ⊎-comm σ' ⟩ E))))

  eval : ℕ → Exp a Γ → ε[ M Γ [] (Val a) ]

  eval n unit = do
    return tt

  eval n (var refl) = do
    (v :⟨ σ ⟩: nil) ← ask
    case ⊎-id⁻ʳ σ of λ where
      refl → return v

  eval n (lam a e) = do
    env ← ask
    return (clos e env)

  eval n (ap (f ×⟨ Γ≺ ⟩ e)) = do
    v ← frame (⊎-comm Γ≺) (►eval n e)
    eval⊸ n f v

  eval n (pairs (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (►eval n e₁)
    v₂⋆v₂ ← ►eval n e₂ & v₁
    return (pairs (✴-swap v₂⋆v₂))

  eval n (letpair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    pairs (v₁ ×⟨ σ ⟩ v₂) ← frame Γ≺ (►eval n e₁)
    empty ← prepend (cons (v₁ ×⟨ σ ⟩ singleton v₂))
    ►eval n e₂

  eval n (send (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (►eval n e₁)
    cref φ ×⟨ σ ⟩ v₁ ← ►eval n e₂ & v₁
    φ' ← ⟪ send (φ ×⟨ σ ⟩ v₁) ⟫
    return (cref φ')

  eval n (recv e) = do
    cref φ ← ►eval n e
    v ×⟨ σ ⟩ φ' ← ⟪ receive φ ⟫
    return (pairs (cref φ' ×⟨ ⊎-comm σ ⟩ v))

  eval n (fork e) = do 
    clos body env ← ►eval n e
    empty ←
      ⟪ fork (app (runReader (cons (tt ×⟨ ⊎-idˡ ⟩ env))) (►eval n body) ⊎-idʳ) ⟫
    return tt

  eval n (terminate e) = do
    cref φ ← ►eval n e
    empty ← ⟪ close φ ⟫
    return tt
