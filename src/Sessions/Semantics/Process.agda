module Sessions.Semantics.Process where

open import Level
open import Size
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Bool

open import Function
open import Relation.Unary hiding (Empty)
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Binary.PropositionalEquality

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Commands

open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Construct.Market
open import Relation.Ternary.Separation.Construct.Product
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Bigstar
open import Relation.Ternary.Separation.Monad.Free Cmd δ
open import Relation.Ternary.Separation.Monad.State
open import Relation.Ternary.Separation.Monad.Error

open Monads using (Monad; str; typed-str)
open Monad {{...}}

data Exc : Set where
  outOfFuel : Exc
  delay     : Exc

open import Sessions.Semantics.Runtime delay
open import Sessions.Semantics.Communication delay

data Thread : Pred RCtx 0ℓ where
  forked :         ∀[ Comp unit ⇒ Thread ]
  main   : ∀ {a} → ∀[ Comp a ⇒ Thread ] 

Pool : Pred RCtx 0ℓ
Pool = Bigstar Thread

St = Π₂ Pool ✴ Channels

open ExceptMonad {A = RCtx} Exc
open StateWithErr {C = RCtx} Exc

onPool : ∀ {P} → ∀[ (Pool ─✴ Except Exc (P ✴ Pool)) ⇒ State? St P ]
app (onPool f) (lift (snd pool ×⟨ σ , σ₁ ⟩ chs) k) (offerᵣ σ₂) with resplit σ₂ σ₁ k
... | _ , _ , τ₁ , τ₂ , τ₃ =
  case app f pool τ₁ of λ where
    (error e) → partial (inj₁ e)
    (✓ (p ×⟨ σ₃ ⟩ p')) →
      let _ , _ , τ₄ , τ₅ , τ₆ = resplit σ₃ τ₂ τ₃
      in return (inj p ×⟨ offerᵣ τ₄ ⟩ lift (snd p' ×⟨ σ , τ₅ ⟩ chs) τ₆)

onChannels : ∀ {P} → ∀[ State? Channels P ⇒ State? St P ]
app (onChannels f) μ (offerᵣ σ₃) with ○≺●ᵣ μ
... | inj pool ×⟨ offerᵣ σ₄ ⟩ chs with ⊎-assoc σ₃ (⊎-comm σ₄)
... | _ , τ₁ , τ₂ = do
  px ×⟨ σ₄ ⟩ ●chs ×⟨ σ₅ ⟩ inj pool ←
    mapM (app f chs (offerᵣ τ₁) &⟨ J Pool ∥ offerₗ τ₂ ⟩ inj pool) ✴-assocᵣ
  return (px ×⟨ σ₄ ⟩ app (○≺●ₗ pool) ●chs (⊎-comm σ₅))

schedule : ∀[ Thread ⇒ State? St Emp ]
schedule thr =
  onPool (wand λ pool σ → return (empty ×⟨ ⊎-idˡ ⟩ (app (append thr) pool σ)))

{- Select the next thread that is not done -}
pop : ε[ State? St (Emp ∪ Thread) ]
pop = 
  onPool (wandit (λ pool →
    case (find isImpure pool) of λ where
      (error e)              → return (inj₁ empty ×⟨ ⊎-idˡ ⟩ pool) 
      (✓ (thr ×⟨ σ ⟩ pool')) → return (inj₂ thr ×⟨ σ ⟩ pool')))
  where
    isImpure : ∀ {Φ} → Thread Φ → Bool
    isImpure = λ where
      (main   (partial (pure _)))   → false
      (forked (partial (pure _)))   → false
      (main   (partial (impure _))) → true
      (forked (partial (impure _))) → true

module _ where

  handle : ∀ {Φ} → (c : Cmd Φ) → State? St (δ c) Φ
  handle (fork thr)           = schedule (forked thr)
  handle (mkchan α)           = onChannels newChan
  handle (send (ch ×⟨ σ ⟩ v)) = onChannels (app (send! ch) v σ)
  handle (receive ch)         = onChannels (receive? ch)
  handle (close ch)           = onChannels (closeChan ch)

  -- Stepping on main thread and forked threads is slightly different,
  -- because we clean up the results of forked of threads.
  -- We choose to escalate out-of-fuel errors in threads immediately.
  step' : ∀[ Thread ⇒ State? St Emp ]
  step' (main (partial c)) = do
    c'@(impure _) ← step handle c
      where
        (pure (inj₁ e))   → raise outOfFuel
        v@(pure (inj₂ _)) → schedule (main (partial v))
    schedule (main (partial c'))
  step' (forked (partial c)) = do
    c'@(impure _) ← step handle c
      where
        (pure (inj₁ e))  → raise outOfFuel
        (pure (inj₂ tt)) → return empty
    schedule (forked (partial c'))

  -- Run a pool of threads in round-robing fashion
  -- until all have terminated, or fuel runs out
  run : ℕ → ε[ State? St Emp ] 
  run zero    = raise outOfFuel
  run (suc n) = do
    inj₂ thr ← pop
      -- if we cannot pop a thunked thread, we're done
      where inj₁ empty → return empty

    -- otherwise we take a step
    empty ← step' thr 

    -- rinse and repeat
    run n
