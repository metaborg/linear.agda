module Relation.Unary.Separation.Bigstar where

open import Level
open import Data.Bool
open import Data.Product
open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Error
open import Relation.Unary.Separation.Morphisms
open Monads

module _
  {a p} {A : Set a} (P : Pred A p)
  {{ r : RawSep A }} {u} {{ _ : IsUnitalSep r u }} where

  data Bigstar : SPred (a ⊔ p) where
    emp  : ε[ Bigstar ]
    cons : ∀[ P ✴ Bigstar ⇒ Bigstar ]

module _
  {a} {A : Set a} {P : Pred A a}
  {{ r : RawSep A }} {u} {{ _ : IsUnitalSep r u }} where

  [_] : ∀[ P ⇒ Bigstar P ]
  [ px ] = cons (px ×⟨ ⊎-idʳ ⟩ emp)

  head : ∀[ Bigstar P ⇒ Err (P ✴ Bigstar P) ]
  head emp = error
  head pool@(cons (px ×⟨ σ ⟩ pxs)) = do
    th₂ ×⟨ σ ⟩ pool' ×⟨ σ₂ ⟩ th₁ ← mapM (head pxs &⟨ ⊎-comm σ ⟩ px) ✴-assocᵣ
    return (th₂ ×⟨ σ ⟩ cons (th₁ ×⟨ ⊎-comm σ₂ ⟩ pool'))

  find : (∀ {Φ} → P Φ → Bool) → ∀[ Bigstar P ⇒ Err (P ✴ Bigstar P) ]
  find f emp = error
  find f (cons (px ×⟨ σ ⟩ pxs)) =
    if f px
      then return (px ×⟨ σ ⟩ pxs)
      else do
        px' ×⟨ σ₁ ⟩ pxs' ×⟨ σ₂ ⟩ px ← mapM (find f pxs &⟨ P ∥ ⊎-comm σ ⟩ px) ✴-assocᵣ
        return (px' ×⟨ σ₁ ⟩ cons (px ×⟨ ⊎-comm σ₂ ⟩ pxs')) 

  append : ∀[ P ⇒ Bigstar P ─✴ Bigstar P ]
  app (append px) emp σ rewrite ⊎-id⁻ʳ σ = [ px ]
  app (append px) (cons (qx ×⟨ σ₁ ⟩ pxs)) σ =
    let _ , σ₂ , σ₃ = ⊎-unassoc σ (⊎-comm σ₁)
        qxs = app (append px) pxs σ₂
    in cons (qx ×⟨ ⊎-comm σ₃ ⟩ qxs)
