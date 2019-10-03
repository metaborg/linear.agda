module Relation.Unary.Separation.Construct.List {a} {A : Set a} where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
open import Data.List.Relation.Ternary.Interleaving.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)
open import Relation.Unary.Separation

private C = List A

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

instance list-has-sep : IsSep separation
list-has-sep = record
  { ⊎-comm = I.swap
  ; ⊎-assoc = interleaving-assoc
  }

instance list-is-unital : IsUnitalSep _ _
IsUnitalSep.isSep list-is-unital               = list-has-sep
IsUnitalSep.⊎-idˡ list-is-unital               = right (≡⇒≋ P.refl)
IsUnitalSep.⊎-id⁻ˡ list-is-unital []           = refl
IsUnitalSep.⊎-id⁻ˡ list-is-unital (refl ∷ʳ px) = cong (_ ∷_) (⊎-id⁻ˡ px)

instance list-has-concat : IsConcattative separation
IsConcattative._∙_ list-has-concat = _++_
IsConcattative.⊎-∙ₗ list-has-concat {Φₑ = []} ps = ps
IsConcattative.⊎-∙ₗ list-has-concat {Φₑ = x ∷ Φₑ} ps = consˡ (⊎-∙ₗ ps)

instance list-unitalsep : UnitalSep _
list-unitalsep = record
  { isUnitalSep = list-is-unital }

instance list-resource : MonoidalSep _
list-resource = record
  { sep = separation
  ; isSep = list-has-sep
  ; isUnitalSep   = list-is-unital
  ; isConcat      = list-has-concat
  ; monoid = ++-isMonoid }

instance list-positive : IsPositive separation
list-positive = record
  { ⊎-εˡ = λ where [] → refl }

{- We can split All P xs over a split of xs -}
module All {v} {V : A → Set v} where

  open import Data.List.All

  all-split : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊎ Γ₂ ≣ Γ → All V Γ → All V Γ₁ × All V Γ₂
  all-split [] [] = [] , []
  all-split (consˡ s) (px ∷ vs) = let xs , ys = all-split s vs in px ∷ xs , ys
  all-split (consʳ s) (px ∷ vs) = let xs , ys = all-split s vs in xs , px ∷ ys


{- Useful predicates -}
module _ where

  Just : A → Pred (List A) a
  Just t = Exactly (t ∷ ε)

  -- Membership
  _∈_ : A → Pred (List A) a
  a ∈ as = [ a ] ≤ as

module _ {b} {B : Set b} {{r : RawSep B}} {u} {{s : IsUnitalSep r u}} where

  repartition : ∀ {p} {P : A → Pred B p} {Σ₁ Σ₂ Σ : List A} →
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
