open import Relation.Unary.Separation

module Relation.Unary.Separation.Monad.CompleteUpdate
  {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }}
  where

open import Function
open import Level hiding (Lift)
open import Data.Product
open import Data.Unit using (⊤)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Market

open Monads {{ bs = record { Carrier = A × A } }} (id-morph (A × A))
open ⟰_

module Update where
  private bind' : ∀ {p q} {P : Pred (A × A) p} {Q : Pred (A × A) q} → ∀[ (P ─✴ ⟰ Q) ⇒ (⟰ P ─✴ ⟰ Q) ]
  updater (app (bind' f) c σ) fr with ⊎-assoc (⊎-comm σ) fr
  ... | xs , σ₂ , σ₃ with updater c σ₂
  ... | ys , zs , σ₄ , px with ⊎-unassoc σ₄ σ₃ 
  ... | _ , σ₅ , σ₆ = updater (app f px (⊎-comm σ₅)) σ₆

  ⟰-monad : Monad ⊤ a (λ _ _ → ⟰_)
  updater (Monad.return ⟰-monad px) fr = -, -, fr , px
  Monad.bind ⟰-monad = bind'

{- updates with failure -}
module UpdateWithFailure where

  open import Relation.Unary.Separation.Monad.Error
  open import Data.Sum

  ⟰? : Pt (A × A) a
  ⟰? P = ⟰ (Err P)

  instance ⟰?-monad : Monad ⊤ a (λ _ _ → ⟰?)
  Monad.return ⟰?-monad px = Monad.return Update.⟰-monad (return px)
  updater (app (Monad.bind ⟰?-monad f) m σ) fr with ⊎-assoc (⊎-comm σ) fr
  ... | _ , σ₂ , σ₃ with updater m σ₂
  ... | _ , _ , τ₁ , error  = -, -, fr , error
  ... | _ , _ , τ₁ , partial (inj₂ v) with ⊎-unassoc τ₁ σ₃
  ... | _ , τ₃ , τ₄ = updater (app f v (⊎-comm τ₃)) τ₄

  ⟰error : ∀ P → ∀[ ⟰? P ] 
  updater (⟰error _) fr = -, -, fr , error
