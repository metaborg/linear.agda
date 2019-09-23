open import Relation.Unary hiding (_∈_)
open import Data.List
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

module Relation.Unary.Separation.Monad.State.Heap 
  {ℓ} {T : Set ℓ} 
  (V : T → Pred (List T) ℓ) 
  where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
import Relation.Binary.HeterogeneousEquality as HEq
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad

open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
  
Cells : Pred (List T × List T) ℓ
Cells (Σ , Φ) = Allstar V Σ Φ

open import Relation.Unary.Separation.Monad.State Cells public

-- Creating a reference to a new cell, filled with a given value.
-- Note that in the market monoid this is pure!
-- Because we get a reference that consumes the freshly created resource.
mkref : ∀ {a} → ∀[ V a ⇒ⱼ State (Just a) ]
app (mkref v) (lift st σ₁) (offerᵣ σ₂) =
  let _ , τ₁ , τ₂ = ⊎-unassoc σ₁ σ₂ 
  in inj refl
    ×⟨ offerᵣ ⊎-∙ ⟩
  lift (cons (v ×⟨ ⊎-comm τ₁ ⟩ st)) (⊎-∙ᵣ τ₂)

-- A linear read on a store: you lose the reference.
-- This is pure, because with the reference being lost, the cell is destroyed: no resources leak.
read : ∀ {a} → ∀[ Just a ⇒ⱼ State (V a) ]
app (read refl) (lift st σ₁) (offerᵣ σ₂) with ⊎-assoc σ₂ (⊎-comm σ₁)
... | _ , σ₃ , σ₄ with repartition σ₃ st
... | cons (v ×⟨ σ₅ ⟩ nil) ×⟨ σ₆ ⟩ st' with ⊎-id⁻ʳ σ₅ | ⊎-assoc (⊎-comm σ₆) (⊎-comm σ₄)
... | refl | _ , τ₁ , τ₂ = inj v ×⟨ offerᵣ τ₂ ⟩ lift st' τ₁

-- Writing into a cell, returning the current contents
write : ∀ {a b} → ∀[ Just b ✴ (V a) ⇒ⱼ State (Just a ✴ V b) ]
app (write (refl ×⟨ σ₁ ⟩ v)) (lift st σ₂) (offerᵣ σ₃) with ⊎-assoc (⊎-comm σ₁) σ₃
-- first we reassociate the arguments in the order that we want to piece it back together
... | _ , τ₁ , τ₂ with ⊎-assoc (⊎-comm τ₁) (⊎-comm σ₂)
... | _ , τ₃ , τ₄ with ⊎-assoc τ₂ τ₃
... | _ , τ₅ , τ₆
-- then we reorganize the store internally to take out the unit value
  with repartition τ₅ st
... | cons (vb ×⟨ σ₅ ⟩ nil) ×⟨ σ₆ ⟩ st' rewrite ⊎-id⁻ʳ σ₅ = 
  let 
    _ , κ₁ , κ₂ = ⊎-unassoc τ₄ (⊎-comm σ₆) 
    _ , κ₃ , κ₄ = ⊎-assoc κ₂ (⊎-comm τ₆)
  in inj (refl ×⟨ consˡ ⊎-idˡ ⟩ vb) ×⟨ offerᵣ (consˡ κ₄) ⟩ lift (cons (v ×⟨ κ₁ ⟩ st')) (consʳ κ₃)

-- A linear (strong) update on the store
update! : ∀ {a b} → ∀[ Just a ✴ (V a ─✴ⱼ State (V b)) ⇒ⱼ State (Just b) ]
update! {a} {b} (ptr ×⟨ σ ⟩ f) = do
  a ×⟨ σ₁ ⟩ f ← str _ (read ptr ×⟨ j-map σ ⟩ inj f)
  b           ← app f a (⊎-comm σ₁)
  mkref b
