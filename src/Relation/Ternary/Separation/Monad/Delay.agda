module Relation.Ternary.Separation.Monad.Delay where

open import Level
open import Function
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer hiding (_⊔_)
open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms

open import Codata.Delay as D using (now; later) public
open import Data.Unit
open Monads

module _ {ℓ}
  {C : Set ℓ} {u}
  {{r : RawSep C}}
  {{us : IsUnitalSep r u}}
 where

  Delay : ∀ {ℓ} i → Pt C ℓ
  Delay i P c = D.Delay (P c) i

  instance
    delay-monad : ∀ {i} → Monad ⊤ ℓ (λ _ _ → Delay i)
    Monad.return delay-monad px = D.now px
    app (Monad.bind delay-monad f) ►px σ = D.bind ►px λ px → app f px σ
