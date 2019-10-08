module Sessions.Semantics.Runtime where

open import Prelude hiding (_∷ʳ_; lift; Lift)
import Data.List as L

open import Relation.Unary hiding (Empty; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Commands
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Error
open import Relation.Unary.Separation.Monad.State

open import Relation.Unary.Separation.Construct.ListOf Runtype
open StateTransformer {C = RCtx} Err

module _ where
  module _ {C : Set} {{ r : RawSep C }} {u} {{ _ : IsUnitalSep r u }} where
    open Monads.Monad {{ bs = record { Carrier = C }}} {j = id-morph C } err-monad public

  data _⇜_ : SType → SType → Pred RCtx 0ℓ where
    emp  : ∀ {α} → (α ⇜ α) ε
    cons : ∀ {a} → ∀[ CVal a ✴ (β ⇜ γ) ⇒ ((a ¿ β) ⇜ γ) ]

  _⇝_ = flip _⇜_

  private
    -- It is crucial for type-safety that this is evident
    send-lemma : ∀[ ((a ! β) ⇜ γ) ⇒ Empty (γ ≡ a ! β) ]
    send-lemma emp = emp refl

  record Link (α γ : SType) Φ : Set where
    constructor link
    field
      {β₁ β₂} : SType
      duals   : β₂ ≡ β₁ ⁻¹
      buffers : (α ⇜ β₁ ✴ β₂ ⇝ γ) Φ

  revLink : ∀[ Link α γ ⇒ Link γ α ]
  revLink (link refl buffers) = link (sym dual-involutive) (✴-swap buffers)

  push : ∀[ CVal a ✴ γ ⇜ (a ¿ β) ⇒ γ ⇜ β ]
  push (v ×⟨ σ₁ ⟩ emp) = cons (v ×⟨ σ₁ ⟩ emp)
  push (v ×⟨ σ₁ ⟩ cons (w ×⟨ σ₂ ⟩ b)) with ⊎-assoc σ₂ (⊎-comm σ₁)
  ... | _ , σ₃ , σ₄ with push (v ×⟨ ⊎-comm σ₄ ⟩ b)
  ... | b' = cons (w ×⟨ σ₃ ⟩ b')

  send-into : ∀[ CVal a ✴ Link α (a ! β) ⇒ Link α β ]
  send-into (v ×⟨ σ ⟩ link {x ¿ β₁} refl (px ×⟨ σ₁ ⟩ emp)) rewrite ⊎-id⁻ʳ σ₁ =
    link refl ((push (v ×⟨ σ ⟩ px)) ×⟨ ⊎-idʳ ⟩ emp)

  recvₗ : ∀[ Link (a ¿ β) γ ⇒ Err (CVal a ✴ Link β γ) ]
  recvₗ c@(link refl (emp ×⟨ _ ⟩ _)) = error
  recvₗ (link refl (cons (v ×⟨ σ₁ ⟩ bₗ) ×⟨ σ₂ ⟩ bᵣ)) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
    in return (v ×⟨ σ₃ ⟩ (link refl (bₗ ×⟨ σ₄ ⟩ bᵣ)))

  recvᵣ : ∀[ Link γ (a ¿ β) ⇒ Err (CVal a ✴ Link γ β) ]
  recvᵣ l = do
    v ×⟨ σ ⟩ l' ← recvₗ (revLink l)
    return (v ×⟨ σ ⟩ revLink l')

  data Channel : Runtype → Pred RCtx 0ℓ where
    chan : ∀[ Link α γ ⇒ Channel (chan α γ) ]

  data Li : SType → Pred (RCtx × RCtx) 0ℓ where
    ln : ∀[ Link α β ⇒ curry (Li α) [ chan α γ ] ]

  data Ch : Pred (RCtx × RCtx) 0ℓ where
    chan : ∀ {τ} → ∀[ Channel τ ⇒ curry Ch [ τ ] ]

  Channels' = Allstar (uncurry Link)

  ⟦_⟧ : List (SType × SType) → RCtx
  ⟦ xs ⟧ = L.map (uncurry chan) xs

  data Channels : RCtx → Pred RCtx 0ℓ where
    channels : ∀ {xs ys} → Channels' xs ys → Channels ⟦ xs ⟧ ys

  Chs : Pred (RCtx × RCtx) 0ℓ
  Chs = uncurry (Allstar Channel)

  merge : ∀[ Chs ⇒ Chs ─✴ Chs ]
  app (merge chs₁) (cons (ch ×⟨ σ₂ ⟩ chs₂)) (to-right σ₁ , σ₃) =
    let _ , σ₄ , σ₅ = ⊎-assoc σ₂ (⊎-comm σ₃) in cons (ch ×⟨ σ₄ ⟩ app (merge chs₁) chs₂ (σ₁ , ⊎-comm σ₅))
  app (merge (cons (ch ×⟨ σ₂ ⟩ chs₁))) chs₂@(cons _) (to-left σ₁ , σ₃) =
    let _ , σ₄ , σ₅ = ⊎-assoc σ₂ σ₃ in cons (ch ×⟨ σ₄ ⟩ app (merge chs₁) chs₂ (σ₁ , σ₅))
  app (merge chs₁@(cons _)) nil (to-left σ₁ , σ₃) with ⊎-id⁻ʳ σ₁ | ⊎-id⁻ʳ σ₃
  ... | refl | refl = chs₁
  app (merge nil) nil ([] , []) = nil

  -- improbable
  app (merge (cons x₁)) (cons (() ×⟨ σ₂ ⟩ chs₂)) (divide lr σ , σ₃)
  app (merge (cons x₁)) (cons (() ×⟨ σ₂ ⟩ chs₂)) (divide rl σ , σ₃)

  emptyChannel : ε[ Channel (chan α (α ⁻¹)) ]
  emptyChannel = chan (link refl (emp ×⟨ ⊎-∙ ⟩ emp))

  newChan : ε[ State Chs (Endptr α ✴ Endptr (α ⁻¹)) ]
  app newChan (lift chs k) σ with ⊎-id⁻ˡ σ
  ... | refl = return (
   (inj (point ×⟨ divide lr ⊎-idˡ ⟩ point))
      ×⟨ offerᵣ ⊎-∙ ⟩
   lift (cons (emptyChannel ×⟨ ⊎-idˡ ⟩ chs)) (⊎-∙ₗ k))
