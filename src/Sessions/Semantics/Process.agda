module Sessions.Semantics.Process where

open import Level
open import Size
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Codata.Stream
import Data.List as List

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
open import Relation.Unary.Separation.Monad.Free Cmd δ

open import Relation.Unary.Separation.Monad.State
open import Relation.Unary.Separation.Monad.Error
open import Relation.Binary.PropositionalEquality

open StateMonad
open StateTransformer {C = RCtx} Err using ()
  renaming (State to State?; state-monad to state?-monad)

Pool : Pred RCtx 0ℓ
Pool = Bigstar (⋃[ a ∶ _ ] Thread a)

{- Select the next thread that is not done, or return the pool unchanged if none exist -}
next : ∀[ Pool ⇒ (Pool ∪ ((⋃[ a ∶ _ ] Thread a) ✴ Pool)) ]
next emp = inj₁ emp
next pool@(cons (th@(_ , pure v) ×⟨ σ ⟩ thrs)) with next thrs
... | inj₁ _ = inj₁ pool
... | inj₂ (thr ×⟨ σ₂ ⟩ thrs') with ⊎-unassoc σ (⊎-comm σ₂)
... | _ , σ₃ , σ₄ = inj₂ (thr ×⟨ ⊎-comm σ₄ ⟩ cons (th ×⟨ σ₃ ⟩ thrs'))
next (cons pr@((_ , impure x) ×⟨ _ ⟩ _)) = inj₂ pr

St = Π₂ Pool ✴ Channels

M : PT _ _ 0ℓ 0ℓ
M = State St

M? : PT _ _ 0ℓ 0ℓ
M? = State? St

liftComm : ∀ {P} → ∀[ State? Channels P ⇒ M? P ]
liftComm = {!!}

schedule : ∀[ Thread a ⇒ⱼ M? Emp ]
app (schedule thr) (lift (snd pool ×⟨ σ₁ , σ₂ ⟩ chs) k) (offerᵣ σ₃) with ⊎-id⁻ˡ σ₁
... | refl with resplit σ₃ σ₂ k
... | _ , _ , τ₁ , τ₂ , τ₃ with ⊎-assoc τ₂ (⊎-comm τ₃)
... | _ , τ₄ , τ₅ =
  ✓ (inj empty ×⟨ ⊎-idˡ ⟩ lift (snd (cons ((-, thr) ×⟨ τ₁ ⟩ pool)) ×⟨ ⊎-idˡ , ⊎-comm τ₅ ⟩ chs) τ₄)

recoverWith : ∀ {P} → ∀[ M P ⇒ M? P ⇒ M P ]
app (recoverWith mq mp) μ σ with app mp μ σ
... | error = app mq μ σ
... | ✓ px  = px

pop : ∀[ M? (⋃[ a ∶ _ ] Thread a) ]
pop = {!!}

open Monads using (Monad; str; typed-str)

module _ where
  open Monad {{...}}

  step : ∀[ Thread a ⇒ⱼ M? (Thread a) ] 

  step (pure v)   = do
    return (pure v)

  step (impure (send args@(ch ×⟨ σ ⟩ v) ×⟨ σ₁ ⟩ κ)) = do
    app (mapM′ κ) (liftComm (app (send! ch) v σ )) (demand (⊎-comm σ₁))

  step (impure (receive ch ×⟨ σ₁ ⟩ κ)) = do
    p×v ×⟨ σ₂ ⟩ κ ← liftComm (receive? ch) &⟨ Cont (receive ch) (Val _) ∥ demand σ₁ ⟩ κ
    return (app κ (✴-swap p×v) (⊎-comm σ₂))

  step (impure (close ch   ×⟨ σ₁ ⟩ κ)) = do
    emp✴κ ← liftComm (closeChan ch) &⟨ Cont (close ch) (Val _) ∥ demand σ₁ ⟩ κ
    return (apply (✴-swap emp✴κ))

  step (impure (fork thr ×⟨ σ₁ ⟩ κ)) = do
    emp✴κ ← schedule thr &⟨ Cont (fork thr) (Val _) ∥ demand σ₁ ⟩ κ
    return (apply (✴-swap emp✴κ))

  {- Run a pool of threads until all have terminated -}
  {-# NON_TERMINATING #-}
  run : ∀[ M Emp ] 
  run = do
    recoverWith run (do
      (_ , thr) ← pop
      thr'      ← step thr
      schedule thr')
