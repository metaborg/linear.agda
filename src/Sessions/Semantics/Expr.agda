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

open ReaderTransformer id-morph Val Free renaming (Reader to M)
open Monads using (Monad; str; _&_)
open Monad reader-monad

{-# TERMINATING #-}
mutual
  eval⊸ : ∀ {Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒ⱼ M Γ [] (Val b) ]
  eval⊸ e v = do
    (clos e env) ×⟨ σ₂ ⟩ v ← eval e & v
    empty                  ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
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
    v₂⋆v₂ ← eval e₂ & v₁
    return (pairs (✴-swap v₂⋆v₂))

  eval (letpair (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    pairs (v₁ ×⟨ σ ⟩ v₂) ← frame Γ≺ (eval e₁)
    empty ← prepend (cons (v₁ ×⟨ σ ⟩ singleton v₂))
    eval e₂

  eval (send (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    v₁ ← frame Γ≺ (eval e₁)
    cref φ ×⟨ σ ⟩ v₁ ← eval e₂ & v₁
    φ' ← liftM  ⟪ send (φ ×⟨ σ ⟩ v₁) ⟫
    return (cref φ')

  eval (recv e) = do
    cref φ ← eval e
    v ×⟨ σ ⟩ φ' ← liftM  ⟪ receive φ ⟫
    return (pairs (cref φ' ×⟨ ⊎-comm σ ⟩ v))

  eval (fork e) = do 
    clos body env ← eval e
    empty ← liftM ⟪ fork (app (runReader (cons (tt ×⟨ ⊎-idˡ ⟩ env))) (eval body) ⊎-idʳ) ⟫
    return tt

  eval (terminate e) = do
    cref φ ← eval e
    empty ← liftM ⟪ close φ ⟫
    return tt
