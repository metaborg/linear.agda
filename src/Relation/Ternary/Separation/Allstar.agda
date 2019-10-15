{-# OPTIONS --safe #-}
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Allstar
  {i} {I : Set i}
  {c} {C : Set c} {{rc : RawSep C}} {u} {{sc : IsUnitalSep rc u}}
  where

open import Level
open import Data.Product
open import Data.List hiding (concat)
open import Relation.Unary

{- Inductive separating forall over a list -}
module _ {ℓ} where
  data Allstar (P : I → Pred C ℓ) : List I → SPred (ℓ ⊔ c ⊔ i) where
    nil  :            ε[ Allstar P [] ]
    cons : ∀ {x xs} → ∀[ P x ✴ Allstar P xs ⇒ Allstar P (x ∷ xs) ]

  -- not typed well in non-pattern positions
  infixr 5 _:⟨_⟩:_
  pattern _:⟨_⟩:_ x p xs = cons (x ×⟨ p ⟩ xs)

  singleton : ∀ {P x} → ∀[ P x ⇒ Allstar P [ x ] ]
  singleton v = cons (v ×⟨ ⊎-idʳ ⟩ nil)

  open import Relation.Ternary.Separation.Construct.List I
  open import Data.List.Relation.Ternary.Interleaving.Propositional as I

  repartition : ∀ {P} {Σ₁ Σ₂ Σ} →
                Σ₁ ⊎ Σ₂ ≣ Σ → ∀[ Allstar P Σ ⇒ Allstar P Σ₁ ✴ Allstar P Σ₂ ]
  repartition [] nil   = nil ×⟨ ⊎-idˡ ⟩ nil
  repartition (consˡ σ) (cons (a ×⟨ σ′ ⟩ qx)) = 
    let
      xs ×⟨ σ′′ ⟩ ys = repartition σ qx
      _ , τ₁ , τ₂    = ⊎-unassoc σ′ σ′′
    in (cons (a ×⟨ τ₁ ⟩ xs)) ×⟨ τ₂ ⟩ ys
  repartition (consʳ σ) (cons (a ×⟨ σ′ ⟩ qx)) =
    let
      xs ×⟨ σ′′ ⟩ ys = repartition σ qx
      _ , τ₁ , τ₂    = ⊎-unassoc σ′ (⊎-comm σ′′)
    in xs ×⟨ ⊎-comm τ₂ ⟩ (cons (a ×⟨ τ₁ ⟩ ys))

  concat : ∀ {P} {Γ₁ Γ₂} → ∀[ Allstar P Γ₁ ✴ Allstar P Γ₂ ⇒ Allstar P (Γ₁ ++ Γ₂) ] 
  concat (nil ×⟨ s ⟩ env₂) rewrite ⊎-id⁻ˡ s = env₂
  concat (cons (v ×⟨ s ⟩ env₁) ×⟨ s' ⟩ env₂) =
    let _ , eq₁ , eq₂ = ⊎-assoc s s' in
    cons (v ×⟨ eq₁ ⟩ (concat (env₁ ×⟨ eq₂ ⟩ env₂)))
