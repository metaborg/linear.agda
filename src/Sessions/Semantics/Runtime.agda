module Sessions.Semantics.Runtime where

open import Prelude
open import Data.Maybe as May

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

open StateTransformer {C = RCtx} Err

private
  module _ {C : Set} {{ r : RawSep C }} {u} {{ _ : IsUnitalSep r u }} where
    open Monads.Monad (err-monad {A = C}) public
    open Monads using (str) public

module _ where
  data _⇜_ : SType → SType → Pred RCtx 0ℓ where
    emp  : ∀ {α} → (α ⇜ α) ε
    cons : ∀ {a} → ∀[ Val a ✴ (β ⇜ γ) ⇒ ((a ¿ β) ⇜ γ) ]

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

  push : ∀[ Val a ✴ γ ⇜ (a ¿ β) ⇒ γ ⇜ β ]
  push (v ×⟨ σ₁ ⟩ emp) = cons (v ×⟨ σ₁ ⟩ emp)
  push (v ×⟨ σ₁ ⟩ cons (w ×⟨ σ₂ ⟩ b)) with ⊎-assoc σ₂ (⊎-comm σ₁)
  ... | _ , σ₃ , σ₄ with push (v ×⟨ ⊎-comm σ₄ ⟩ b)
  ... | b' = cons (w ×⟨ σ₃ ⟩ b')

  pull : ∀[ γ ⇝ (a ¿ β) ⇒ Err (Val a ✴ γ ⇝ β) ]
  pull emp                  = error
  pull (cons (v ×⟨ σ ⟩ vs)) = return (v ×⟨ σ ⟩ vs)

  send-into : ∀[ Val a ✴ Link α (a ! β) ⇒ Link α β ]
  send-into (v ×⟨ σ ⟩ link {x ¿ β₁} refl (px ×⟨ σ₁ ⟩ emp)) rewrite ⊎-id⁻ʳ σ₁ =
    link refl ((push (v ×⟨ σ ⟩ px)) ×⟨ ⊎-idʳ ⟩ emp)

  recvₗ : ∀[ Link (a ¿ β) γ ⇒ Err (Val a ✴ Link β γ) ]
  recvₗ c@(link refl (bₗ ×⟨ τ ⟩ bᵣ)) = do
    v ×⟨ σ ⟩ l ← mapM (pull bₗ &⟨ τ ⟩ bᵣ) ✴-assocᵣ
    return (v ×⟨ σ ⟩ link refl l)

  recvᵣ : ∀[ Link γ (a ¿ β) ⇒ Err (Val a ✴ Link γ β) ]
  recvᵣ l = do
    v ×⟨ σ ⟩ l' ← recvₗ (revLink l)
    return (v ×⟨ σ ⟩ revLink l')

  data Recipient : SType → Set where
    rec : Recipient (a ¿ β)
    end : Recipient end

  data Channel : Runtype → Pred RCtx 0ℓ where
    twosided : ∀[ Link α β ⇒ Channel (chan α β) ]
    onesided : ∀[ end ⇝ β  ⇒ Channel (endp β) ]

  Channels' = Allstar Channel
  Channels = uncurry Channels'

  emptyLink : ε[ Link α (α ⁻¹) ]
  emptyLink = link refl (emp ×⟨ ⊎-∙ ⟩ emp)

  emptyChannel : ε[ Channel (chan α (α ⁻¹)) ]
  emptyChannel = twosided (link refl (emp ×⟨ ⊎-∙ ⟩ emp))

  flipChan : ∀ {τ} → ∀[ Channel τ ⇒ Channel (flipped τ) ]
  flipChan (twosided x) = twosided (revLink x)
  flipChan (onesided x) = onesided x

  {- Updating a known endpoint of a channel type -}
  _≔ₑ_ : ∀ {τ} → End α τ → SType → Runtype
  (endp β ∷ [] , divide lr []) ≔ₑ α = chan α β
  (endp β ∷ [] , divide rl []) ≔ₑ α = chan β α
  (         [] , to-left _)    ≔ₑ α = endp α

  {- Updating or closing a known endpoint of a channel type -}
  endp? : Maybe SType → Maybe Runtype
  endp? = May.map endp

  chan? : Maybe SType → Maybe SType → Maybe Runtype
  chan? (just α) β? = maybe (just ∘ chan α) (just (endp α)) β?
  chan? nothing  β? = endp? β?

  _≔?_ : ∀ {τ} → End α τ → Maybe SType → Maybe Runtype
  (endp β ∷ [] , divide lr []) ≔? α = chan? α (just β)
  (endp β ∷ [] , divide rl []) ≔? α = chan? (just β) α
  (         [] , to-left _)    ≔? α = endp? α

  onesided-recipient : ∀ {Φ} → (end ⇝ α) Φ → Recipient α
  onesided-recipient emp      = end
  onesided-recipient (cons x) = rec

  {- Receiving on any receiving end of a channel -}
  chan-receive : ∀ {τ} → (e : End (a ¿ α) τ) →
                 ∀[ Channel τ ⇒ Err (Val a ✴ Channel (e ≔ₑ α)) ]

  chan-receive (._ , divide lr []) (twosided l) = do
    v ×⟨ σ ⟩ l' ← recvₗ l
    return (v ×⟨ σ ⟩ twosided l')

  chan-receive (._ , divide rl []) (twosided l) = do
    v ×⟨ σ ⟩ l' ← recvᵣ l
    return (v ×⟨ σ ⟩ twosided l')

  chan-receive (fst₁ , to-left []) (onesided b) = do
    v ×⟨ σ ⟩ b' ← pull b
    return (v ×⟨ σ ⟩ onesided b')

  {- Sending on any sending end of a channel -}
  chan-send : ∀ {τ} → (e : End (a ! α) τ) →
              ∀[ Channel τ ⇒ Val a ─✴ Channel (e ≔ₑ α) ]

  app (chan-send (_ , divide lr []) (twosided l)) v σ =
    let l' = send-into (v ×⟨ ⊎-comm σ ⟩ revLink l)
    in twosided (revLink l')

  app (chan-send (_ , divide rl []) (twosided l)) v σ =
    let l' = send-into (v ×⟨ ⊎-comm σ ⟩ l)
    in twosided l'

  -- cannot be onesided
  app (chan-send (_ , to-left []  ) (onesided b)) v σ with onesided-recipient b
  ... | ()
