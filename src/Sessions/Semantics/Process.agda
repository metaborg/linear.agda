module Sessions.Semantics.Process where

open import Level
open import Size
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Bool

open import Function
open import Relation.Unary hiding (Empty)
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Binary.PropositionalEquality

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime
open import Sessions.Semantics.Communication

open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Construct.Market
open import Relation.Ternary.Separation.Construct.Product
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Bigstar
open import Relation.Ternary.Separation.Monad.Free Cmd δ
open import Relation.Ternary.Separation.Monad.State
open import Relation.Ternary.Separation.Monad.Error

open StateMonad

open Monads using (Monad; str; typed-str)
open Monad {{...}}

Pool : Pred RCtx 0ℓ
Pool = Bigstar (⋃[ a ∶ _ ] Thread a)

St = Π₂ Pool ✴ Channels

open StateWithErr St

M : PT _ _ 0ℓ 0ℓ
M = State St

M? : PT _ _ 0ℓ 0ℓ
M? = State? St

onPool : ∀ {P} → ∀[ (Pool ─✴ Err (P ✴ Pool)) ⇒ M? P ]
app (onPool f) (lift (snd pool ×⟨ σ , σ₁ ⟩ chs) k) (offerᵣ σ₂) with resplit σ₂ σ₁ k
... | _ , _ , τ₁ , τ₂ , τ₃ =
  case app f pool τ₁ of λ where
    error → error
    (✓ (p ×⟨ σ₃ ⟩ p')) →
      let _ , _ , τ₄ , τ₅ , τ₆ = resplit σ₃ τ₂ τ₃
      in return (inj p ×⟨ offerᵣ τ₄ ⟩ lift (snd p' ×⟨ σ , τ₅ ⟩ chs) τ₆)

onChannels : ∀ {P} → ∀[ State? Channels P ⇒ M? P ]
app (onChannels f) μ (offerᵣ σ₃) with ○≺●ᵣ μ
... | inj pool ×⟨ offerᵣ σ₄ ⟩ chs with ⊎-assoc σ₃ (⊎-comm σ₄)
... | _ , τ₁ , τ₂ = do
  px ×⟨ σ₄ ⟩ ●chs ×⟨ σ₅ ⟩ inj pool ←
    mapM (app f chs (offerᵣ τ₁) &⟨ J Pool ∥ offerₗ τ₂ ⟩ inj pool) ✴-assocᵣ
  return (px ×⟨ σ₄ ⟩ app (○≺●ₗ pool) ●chs (⊎-comm σ₅))

schedule : ∀[ Thread a ⇒ M Emp ]
schedule thr = {!!}
  -- onPool
  --   (wand (λ p σ →
  --     return (empty ×⟨ ⊎-idˡ ⟩ app (append (-, thr)) p σ)))

{- Select the next thread that is not done -}
pop : ε[ M? (⋃[ a ∶ _ ] Thread a) ]
pop = onPool (
  wandit (find λ where
    (_ , pure _) → false
    (_ , impure _) → true))

module _ where

  handle : ∀ {Φ} → (c : Cmd Φ) → M? (δ c) Φ
  handle (fork thr)           = liftState (schedule thr)
  handle (mkchan α)           = onChannels newChan
  handle (send (ch ×⟨ σ ⟩ v)) = onChannels (app (send! ch) v σ)
  handle (receive ch)         = onChannels (receive? ch)
  handle (close ch)           = onChannels (closeChan ch)

  -- Run a pool of threads in round-robing fashion
  -- until all have terminated, or fuel runs out
  run : ℕ → ε[ M Emp ] 
  run zero    = return empty
  run (suc n) = do
    -- if we cannot pop a thread, we're done
    inj₂ (_ , thr) ← try pop
      where inj₁ e → return e

    -- try to make a step, or reschedule if thread is stuck
    empty ← recoverWith (schedule thr) (do
      thr' ← step handle thr
      liftState (schedule thr'))

    run n
