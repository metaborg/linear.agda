open import Relation.Unary
open import Relation.Unary.Separation

module Relation.Unary.Separation.Monad.Free {ℓ} {A : Set ℓ}
  {{r : RawSep A}}
  {u} {{_ : IsUnitalSep r u}}
  (Cmd : Pred A ℓ)
  (δ   : ∀ {Φ} → Cmd Φ → Pred A ℓ)
  where

open import Level
open import Function
open import Data.Unit
open import Data.Product
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Binary.PropositionalEquality

mutual
  Cont : ∀ {Δ} → Cmd Δ → Pred A ℓ → Pred A ℓ
  Cont c P = δ c ─✴ Free P

  data Free : PT A A ℓ ℓ where
    pure   : ∀ {P}   → ∀[ P ⇒ Free P ] 
    impure : ∀ {P}   → ∀[ ∃[ Cmd ]✴ (λ c → Cont c P) ⇒ Free P ]

open Monads {{ bs = record { Carrier = A } }} (id-morph A)

instance
  monad : Monad ⊤ ℓ (λ _ _ → Free)
  Monad.return monad = pure
  app (Monad.bind monad f) (pure x) σ = app f x σ
  app (Monad.bind monad f) (impure (cmd ×⟨ σ₁ ⟩ κ)) σ = 
    let _ , σ₂ , σ₃ = ⊎-assoc σ₁ (⊎-comm σ) in
    impure (cmd ×⟨ σ₂ ⟩ wand λ resp σ₄ → 
      let _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₃) σ₄ in
      app (bind f) (app κ resp τ₂) τ₁)

⟪_⟫ : ∀ {Φ} → (c : Cmd Φ) → Free (δ c) Φ
⟪_⟫ c = impure (c ×⟨ ⊎-idʳ ⟩ wand λ r σ → case ⊎-id⁻ˡ σ of λ where refl → return r  )

