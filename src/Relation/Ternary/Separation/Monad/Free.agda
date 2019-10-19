open import Relation.Unary
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Monad.Free {ℓ} {A : Set ℓ}
  {{r : RawSep A}}
  (Cmd : Pred A ℓ)
  (δ   : ∀ {Φ} → Cmd Φ → Pred A ℓ)
  where

open import Level
open import Function
open import Data.Unit
open import Data.Product
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Binary.PropositionalEquality

mutual
  Cont : ∀ {Δ} → Cmd Δ → Pred A ℓ → Pred A ℓ
  Cont c P = δ c ─✴ Free P

  data Free : PT A A ℓ ℓ where
    pure   : ∀ {P}   → ∀[ P ⇒ Free P ]
    impure : ∀ {P}   → ∀[ ∃[ Cmd ]✴ (λ c → Cont c P) ⇒ Free P ]

module _ {u} {{_ : IsUnitalSep r u}} where
  open Monads
  instance
    free-monad : Monad ⊤ ℓ (λ _ _ → Free)
    Monad.return free-monad = pure
    app (Monad.bind free-monad f) (pure x) σ = app f x σ
    app (Monad.bind free-monad f) (impure (cmd ×⟨ σ₁ ⟩ κ)) σ =
      let _ , σ₂ , σ₃ = ⊎-assoc σ₁ (⊎-comm σ) in
      impure (cmd ×⟨ σ₂ ⟩ wand λ resp σ₄ →
        let _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₃) σ₄ in
        app (bind f) (app κ resp τ₂) τ₁)

  ⟪_⟫ : ∀ {Φ} → (c : Cmd Φ) → Free (δ c) Φ
  ⟪_⟫ c = 
    impure (c ×⟨ ⊎-idʳ ⟩ 
      wand λ r σ → case ⊎-id⁻ˡ σ of λ where refl → return r  )

module _ {B : Set ℓ} {M : PT A B ℓ ℓ} {P : Pred A ℓ} 
  {{rb : RawSep B}} {u} {{_ : IsUnitalSep r u}}
  {{jm : Morphism A B}}
  {{_ : IsUnitalSep rb (Morphism.j jm u)}}
  {{ monad : Monads.Monad {{jm = jm}} ⊤ ℓ (λ _ _ → M) }}
  where

  open Morphism jm
  open Monads.Monad {{jm = jm}} monad
  open Monads {{jm = jm}} using (str; typed-str)

  open import Data.Nat

  -- Unfolding a command tree one step
  step : (cmd : ∀ {Φ} → (c : Cmd Φ) → M (δ c) (j Φ)) → ∀[ Free P ⇒ⱼ M (Free P) ]
  step cmd (pure px) = return (pure px)
  step cmd (impure (c ×⟨ σ ⟩ κ)) = do
    r ×⟨ σ ⟩ κ ← cmd c &⟨ Cont c P ∥ j-⊎ σ ⟩ κ
    return (app κ r (⊎-comm σ))

  -- A fueled generic interpreter for command trees in Free
  interpret : ℕ → ∀[ M P ] → (cmd : ∀ {Φ} → (c : Cmd Φ) → M (δ c) (j Φ)) → ∀[ Free P ⇒ⱼ M P ]
  interpret zero    def cmd f = def
  interpret (suc n) def cmd f = do
    impure f ← step cmd f
      where
        (pure v) → return v
    interpret n def cmd (impure f)
