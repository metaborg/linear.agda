open import Relation.Unary.Separation

module Relation.Unary.Separation.Monad.CompleteUpdate
  {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }}
  where

open import Function
open import Level hiding (Lift)
open import Data.Product
open import Data.Unit using (⊤)

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Market

open Monads {{ bs = record { Carrier = A × A } }} (id-morph (A × A))
open ⇥_


private bind' : ∀ {p q} {P : Pred (A × A) p} {Q : Pred (A × A) q} → ∀[ (P ─✴ ⇥ Q) ⇒ (⇥ P ─✴ ⇥ Q) ]
updater (app (bind' f) c σ) fr k with ⊎-assoc (⊎-comm σ) fr
... | xs , σ₂ , σ₃ with updater c σ₂ k
... | ys , zs , σ₄ , k' , px with ⊎-unassoc σ₄ σ₃ 
... | _ , σ₅ , σ₆ = updater (app f px (⊎-comm σ₅)) σ₆ k'

⇥-monad : Monad ⊤ a (λ _ _ → ⇥_)
updater (Monad.return ⇥-monad px) fr c = -, -, fr , c , px
(Monad.bind ⇥-monad f) =  bind' f
