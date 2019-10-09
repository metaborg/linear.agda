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
open import Sessions.Semantics.Expr using () renaming (Thread to Thread′)
open import Relation.Unary.Separation.Monad.Free Cmd δ

open import Relation.Unary.Separation.Monad.State
open import Relation.Unary.Separation.Monad.Error
open import Relation.Binary.PropositionalEquality

open StateMonad
open StateTransformer {C = RCtx} Err using ()
  renaming (State to State?; state-monad to state?-monad)

Pool : Pred RCtx 0ℓ
Pool = Bigstar (⋃[ a ∶ _ ] Thread a)

St = Channels

M : PT _ _ 0ℓ 0ℓ
M = State St

M? : PT _ _ 0ℓ 0ℓ
M? = State? St

open Monads using (Monad; str)

module _ where
  open Monad (state?-monad {St = St})

  liftComm : ∀ {P} → ∀[ State? Channels P ⇒ M? P ]
  liftComm = {!!}

  step : ∀[ Thread a ⇒ⱼ M? (Thread a) ] 

  step (pure v)   = do
    return (pure v)

  step (impure (send args@(ch ×⟨ σ ⟩ v) ×⟨ σ₁ ⟩ κ)) = do
    ptr ← app (str {Q = Cont (send args) (Val _)} κ)
      (liftComm (app (send! ch) v σ ))
      (demand (⊎-comm σ₁))
    {!!}

  step (impure (receive x ×⟨ σ₁ ⟩ κ)) = {!!}

  step (impure (close x   ×⟨ σ₁ ⟩ κ)) = {!!}

  step (impure (fork x    ×⟨ σ₁ ⟩ κ)) = {!!}

module _ where
  open Monad (state-monad {St = St})

  recoverWith : ∀ {P} → ∀[ M P ⇒ M? P ⇒ M P ]
  app (recoverWith mq mp) μ σ with app mp μ σ
  ... | error = app mq μ σ
  ... | ✓ px  = px

  {- Select the next thread that is not done, or return the pool unchanged if none exist -}
  next : ∀[ Pool ⇒ (Pool ∪ (Thread ✴ Pool)) ]
  next emp = inj₁ emp
  next pool@(cons (th@(pure v) ×⟨ σ ⟩ thrs)) with next thrs
  ... | inj₁ _ = inj₁ pool
  ... | inj₂ (thr ×⟨ σ₂ ⟩ thrs') with ⊎-unassoc σ (⊎-comm σ₂)
  ... | _ , σ₃ , σ₄ = inj₂ (thr ×⟨ ⊎-comm σ₄ ⟩ cons (th ×⟨ σ₃ ⟩ thrs'))
  next (cons pr@(impure x ×⟨ _ ⟩ _)) = inj₂ pr

  {- Run a pool of threads until all have terminated -}
  {-# NON_TERMINATING #-}
  run : ∀[ Pool ⇒ⱼ M Pool ] 
  run pool = do
    case (next pool) of λ where

      (inj₁ pool) → do
        return pool

      (inj₂ (thr ×⟨ σ ⟩ pool)) → do
        pool' ← app (str {Q = Pool} pool)
          (recoverWith (return thr) (step thr)) (demand (⊎-comm σ))

        run (cons pool')

