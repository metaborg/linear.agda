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
  reassoc : ∀ {a b ab c abc : List A} →
            Interleaving a b ab → Interleaving ab c abc →
            ∃ λ bc → Interleaving a bc abc × Interleaving b c bc
  reassoc l (consʳ r)         = let _ , p , q = reassoc l r in -, consʳ p , consʳ q
  reassoc (consˡ l) (consˡ r) = let _ , p , q = reassoc l r in -, consˡ p , q
  reassoc (consʳ l) (consˡ r) = let _ , p , q = reassoc l r in -, consʳ p , consˡ q
  reassoc [] []               = [] , [] , []

  instance ctx-has-sep : IsSep separation
  ctx-has-sep = record
    { ⊎-comm = I.swap
    ; ⊎-assoc = reassoc
    }

  instance ctx-hasUnitalSep : IsUnitalSep _
  IsUnitalSep.isSep ctx-hasUnitalSep                     = ctx-has-sep
  IsUnitalSep.ε ctx-hasUnitalSep                         = []
  IsUnitalSep.⊎-identityˡ ctx-hasUnitalSep               = right (≡⇒≋ P.refl)
  IsUnitalSep.⊎-identity⁻ˡ ctx-hasUnitalSep []           = refl
  IsUnitalSep.⊎-identity⁻ˡ ctx-hasUnitalSep (refl ∷ʳ px) = cong (_ ∷_) (⊎-identity⁻ˡ px)

  instance ctx-concattative : IsConcattative separation
  ctx-concattative = record
    { _∙_ = _++_
    ; ⊎-∙ = λ {Φₗ} {Φᵣ} → ++-disjoint (left (≡⇒≋ P.refl)) (right (≡⇒≋ P.refl))
    }

  instance ctx-unitalsep : UnitalSep _ _
  ctx-unitalsep = record
    { set = record { isEquivalence = ↭-isEquivalence }
    ; isUnitalSep = ctx-hasUnitalSep }

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

