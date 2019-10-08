module Sessions.Semantics.Process where

open import Prelude hiding (lift)
open import Codata.Stream

open import Relation.Unary hiding (Empty)
open import Relation.Unary.PredicateTransformer using (Pt)
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

open import Relation.Unary.Separation.Construct.ListOf Runtype
open import Relation.Unary.Separation.Monad.State

open StateMonad

{- Thread pools -}


Thread : Pred RCtx 0ℓ
Thread = Client Cmd

pattern thread c = client c

Pool : Pred RCtx 0ℓ
Pool = Bigstar Thread

M = State (Π₂ (Pool ✴ Empty (Stream ℕ ∞)) ✴ Channels)

eval : ∀[ M Pool ] 
eval = {!!}

