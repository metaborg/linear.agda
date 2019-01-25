open import Data.List

module Relation.Unary.Separation {a} {A : Set a} (Res : Set) (proj : Res → List A) where

open import Function
open import Level
open import Data.List.Relation.Ternary.Interleaving.Propositional

open import Relation.Unary

-- separating conjunction
infixr 9 _✴_
record _✴_ {ℓ₁ ℓ₂} (P : Pred Res ℓ₁) (Q : Pred Res ℓ₂) Φ : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor _×⟨_⟩_
  field
    {Φₗ Φᵣ} : Res

    p   : P Φₗ
    sep : (Interleaving on proj) Φₗ Φᵣ (proj Φ)
    q   : Q Φᵣ
