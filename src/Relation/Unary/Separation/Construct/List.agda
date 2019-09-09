module Relation.Unary.Separation.Construct.List where

open import Data.Product
open import Data.List
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Unary.Separation

module _ {a} {A : Set a} where
  private
    C = List A

  instance separation : RawSep C
  separation = record { _⊎_≣_ = Interleaving }

  -- TODO add to stdlib
  interleaving-assoc : ∀ {a b ab c abc : List A} →
            Interleaving a b ab → Interleaving ab c abc →
            ∃ λ bc → Interleaving a bc abc × Interleaving b c bc
  interleaving-assoc l (consʳ r)         = let _ , p , q = interleaving-assoc l r in -, consʳ p , consʳ q
  interleaving-assoc (consˡ l) (consˡ r) = let _ , p , q = interleaving-assoc l r in -, consˡ p , q
  interleaving-assoc (consʳ l) (consˡ r) = let _ , p , q = interleaving-assoc l r in -, consʳ p , consˡ q
  interleaving-assoc [] []               = [] , [] , []

  instance ctx-has-sep : IsSep separation
  ctx-has-sep = record
    { ⊎-comm = I.swap
    ; ⊎-assoc = interleaving-assoc
    }

  instance ctx-hasUnitalSep : IsUnitalSep _ _
  IsUnitalSep.isSep ctx-hasUnitalSep               = ctx-has-sep
  IsUnitalSep.⊎-idˡ ctx-hasUnitalSep               = right (≡⇒≋ P.refl)
  IsUnitalSep.⊎-id⁻ˡ ctx-hasUnitalSep []           = refl
  IsUnitalSep.⊎-id⁻ˡ ctx-hasUnitalSep (refl ∷ʳ px) = cong (_ ∷_) (⊎-id⁻ˡ px)

  instance ctx-concattative : IsConcattative separation
  ctx-concattative = record
    { _∙_ = _++_
    ; ⊎-∙ = λ {Φₗ} {Φᵣ} → ++-disjoint (left (≡⇒≋ P.refl)) (right (≡⇒≋ P.refl))
    }

  instance ctx-unitalsep : UnitalSep _
  ctx-unitalsep = record
    { isUnitalSep = ctx-hasUnitalSep }

  instance ctx-resource : MonoidalSep _
  ctx-resource = record
    { sep = separation
    ; isSep = ctx-has-sep
    ; isUnitalSep   = ctx-hasUnitalSep
    ; isConcat      = ctx-concattative }

{- We can split All P xs over a split of xs -}
module All {t v} {T : Set t} {V : T → Set v} where

  open import Data.List.All

  all-split : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊎ Γ₂ ≣ Γ → All V Γ → All V Γ₁ × All V Γ₂
  all-split [] [] = [] , []
  all-split (consˡ s) (px ∷ vs) = let xs , ys = all-split s vs in px ∷ xs , ys
  all-split (consʳ s) (px ∷ vs) = let xs , ys = all-split s vs in xs , px ∷ ys

