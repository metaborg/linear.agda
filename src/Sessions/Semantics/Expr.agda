module Sessions.Semantics.Expr where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Reader
open import Relation.Unary.Separation.Construct.List

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr
open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime

open import Relation.Unary.Separation.Monad.Free Cmd δ

open Reader id-morph Val Free renaming (Reader to M)
open Monads using (Monad; str)
open Monad reader-monad

Thread : Type → Pred SCtx _
Thread a = Free (Val a)

{-# TERMINATING #-}
mutual
  eval⊸ : ∀ {Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M Γ [] (Val b) ]
  eval⊸ e v = do
    clos e env ×⟨ σ₂ ⟩ v ← app (str v) (eval e) ⊎-idʳ
    empty                ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
    eval e

  eval : Exp a Γ → ε[ M Γ [] (Val a) ]

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
    v ← frame (⊎-comm Γ≺) (eval e)
    eval⊸ f v

  eval (pairs (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (eval e₁)
    v₂⋆v₂ ← app (str v₁) (eval e₂) ⊎-idʳ
    return (pairs (✴-swap v₂⋆v₂))

  eval (letpair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    pairs (v₁ ×⟨ σ ⟩ v₂) ← frame Γ≺ (eval e₁)
    empty ← prepend (cons (v₁ ×⟨ σ ⟩ singleton v₂))
    eval e₂

  eval (send (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (eval e₁)
    cref φ ×⟨ σ ⟩ v₁ ← app (str v₁) (eval e₂) ⊎-idʳ
    φ' ← liftM  ⟪ send (φ ×⟨ σ ⟩ v₁) ⟫
    return (cref φ')

  eval (recv e) = do
    cref φ ← eval e
    φ' ×⟨ σ ⟩ v ← liftM  ⟪ receive φ ⟫
    return (pairs (cref φ' ×⟨ σ ⟩ v))

  eval (fork e) = do 
    clos e env ← eval e
    φ ← liftM ⟪ fork (clos e env) ⟫
    return (cref φ)

  eval (terminate e) = do
    cref φ ← eval e
    empty ← liftM ⟪ close φ ⟫
    return tt
