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
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime
open import Sessions.Semantics.Communication
open import Sessions.Semantics.Expr

open import Relation.Unary.Separation.Bigstar
open import Relation.Unary.Separation.Monad.Free Cmd δ
open import Relation.Unary.Separation.Monad.State
open import Relation.Unary.Separation.Monad.Error
open import Relation.Binary.PropositionalEquality

open StateMonad
open StateTransformer {C = RCtx} Err using ()
  renaming (State to State?; state-monad to state?-monad)

open Monads using (Monad; str; typed-str)
open Monad {{...}}

Pool : Pred RCtx 0ℓ
Pool = Bigstar (⋃[ a ∶ _ ] Thread a)

St = Π₂ Pool ✴ Channels

M : PT _ _ 0ℓ 0ℓ
M = State St

M? : PT _ _ 0ℓ 0ℓ
M? = State? St

onPool : ∀ {P} → ∀[ (Pool ─✴ Err (P ✴ Pool)) ⇒ⱼ M? P ]
onPool = {!!}

onChannels : ∀ {P} → ∀[ State? Channels P ⇒ M? P ]
onChannels = {!!}

schedule : ∀[ Thread a ⇒ⱼ M? Emp ]
schedule thr =
  onPool
    (wand (λ p σ →
      return (empty ×⟨ ⊎-idˡ ⟩ app (append (-, thr)) p σ)))

recoverWith : ∀ {P} → ∀[ M P ⇒ M? P ⇒ M P ]
app (recoverWith mq mp) μ σ with app mp μ σ
... | error = app mq μ σ
... | ✓ px  = px

{- Select the next thread that is not done -}
pop : ε[ M? (⋃[ a ∶ _ ] Thread a) ]
pop = onPool (
  wandit (find λ where
    (_ , pure _) → false
    (_ , impure _) → true))

module _ where

  step : ∀[ Thread a ⇒ⱼ M? (Thread a) ] 

  step (pure v)   = do
    return (pure v)

  step (impure (send args@(ch ×⟨ σ ⟩ v) ×⟨ σ₁ ⟩ κ)) = do
    app (mapM′ κ) (onChannels (app (send! ch) v σ )) (demand (⊎-comm σ₁))

  step (impure (receive ch ×⟨ σ₁ ⟩ κ)) = do
    p×v ×⟨ σ₂ ⟩ κ ← onChannels (receive? ch) &⟨ Cont (receive ch) (Val _) ∥ demand σ₁ ⟩ κ
    return (app κ (✴-swap p×v) (⊎-comm σ₂))

  step (impure (close ch   ×⟨ σ₁ ⟩ κ)) = do
    emp✴κ ← onChannels (closeChan ch) &⟨ Cont (close ch) (Val _) ∥ demand σ₁ ⟩ κ
    return (apply (✴-swap emp✴κ))

  step (impure (fork thr ×⟨ σ₁ ⟩ κ)) = do
    emp✴κ ← schedule thr &⟨ Cont (fork thr) (Val _) ∥ demand σ₁ ⟩ κ
    return (apply (✴-swap emp✴κ))

  -- Run a pool of threads in round-robing fashion
  -- until all have terminated, or fuel runs out
  run : ℕ → ε[ M Emp ] 
  run zero    = return empty
  run (suc n) = do
    recoverWith (run n) (do
      (_ , thr) ← pop
      thr'      ← step thr
      schedule thr')
