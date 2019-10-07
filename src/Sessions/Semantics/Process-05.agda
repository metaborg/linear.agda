module Sessions.Semantics.Process-05 where

open import Prelude hiding (_∷ʳ_; lift; Lift)
open import Data.Maybe
open import Data.List.Relation.Ternary.Interleaving
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Equality.Propositional 
open import Data.List.Properties
import Data.List as L

open import Relation.Unary hiding (Empty; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad

open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Error
open import Relation.Unary.Separation.Monad.State
open import Relation.Unary.Separation.Monad.CompleteUpdate

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr
open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime

open import Relation.Unary.Separation.Construct.ListOf Runtype
open UpdateWithFailure

private module Err = Monads.Monad {j = id-morph (Market RCtx)} err-monad

{- Type of actions on a link -}
private
  Action : SType → SType → Pt RCtx 0ℓ
  Action α β P = ⋂[ γ ∶ _ ] (Link α γ ─✴ Err (P ✴ Link β γ))

module _ where
  private jm = id-morph (RCtx × RCtx)
  open Monads  {{ bs =  record { Carrier = RCtx × RCtx } }} jm
  module Idm = Morphism jm

  {- A specification of the update we are performing -}
  _≔_ : ∀ {x} {ys} {zs : List (SType × SType)} → [ endp x ] ⊎ ys ≣ ⟦ zs ⟧ →
               SType → List (SType × SType)
  _≔_ {zs = (_ , r) ∷ zs} (divide lr s) α = (α , r) ∷ zs
  _≔_ {zs = (l , _) ∷ zs} (divide rl s) α = (l , α) ∷ zs
  _≔_ {zs = x ∷ zs}       (to-right s)  α = x ∷ (s ≔ α)

  -- {- Takes an endpointer and the channel list and updates it using a link action -}
  act : ∀ {P α cs xs c₁ c₂ ds} →
        (ptr : [ endp α ] ⊎ ds ≣ ⟦ xs ⟧) → (Action α β P) c₁ → c₁ ⊎ c₂ ≣ cs →
        Channels' xs c₂ → Maybe ([ endp β ] ⊎ ds ≣ ⟦ ptr ≔ β ⟧ × (P ✴ Channels' (ptr ≔ β)) cs)

  act {xs = x ∷ xs} (divide lr ptr) f σ (l :⟨ τ ⟩: chs) with ⊎-unassoc σ τ
  ... | _ , τ₂ , τ₃ with app (f _) l τ₂
  ... | inj₁ _ = nothing
  ... | inj₂ (px ×⟨ τ₄ ⟩ l') with ⊎-assoc τ₄ τ₃
  ... | _ , τ₅ , τ₆ = just (divide lr ptr , px ×⟨ τ₅ ⟩ (cons (l' ×⟨ τ₆ ⟩ chs)))

  act {xs = x ∷ xs} (divide rl ptr) f σ (l :⟨ τ ⟩: chs) with ⊎-unassoc σ τ
  ... | _ , τ₂ , τ₃ with app (f _) (revLink l) τ₂
  ... | inj₁ _ = nothing
  ... | inj₂ (px ×⟨ τ₄ ⟩ l') with ⊎-assoc τ₄ τ₃
  ... | _ , τ₅ , τ₆ = just (divide rl ptr , px ×⟨ τ₅ ⟩ (cons (revLink l' ×⟨ τ₆ ⟩ chs)))

  act {xs = x ∷ xs} (to-right ptr)  f σ (ch :⟨ τ ⟩: chs) with ⊎-unassoc σ (⊎-comm τ)
  ... | _ , τ₁ , τ₂ with act ptr f τ₁ chs
  ... | nothing = nothing
  ... | just (ptr' , px ×⟨ τ₃ ⟩ chs') with ⊎-assoc τ₃ τ₂
  ... | _ , τ₄ , τ₅ = just (to-right ptr' , (px ×⟨ τ₄ ⟩ cons (ch ×⟨ ⊎-comm τ₅ ⟩ chs')))

open StateTransformer {C = RCtx} Err

operate : ∀ {P} → ∀[ Action α β P ⇒ Endptr α ─✴ⱼ State (uncurry Channels) (P ✴ Endptr β) ]
app (app (operate f) point σ₁) (lift (channels chs) k) (offerᵣ σ₂) with ⊎-assoc σ₂ k
... | _ , σ₃ , σ₄ with ⊎-assoc (⊎-comm σ₁) σ₃
... | _ , σ₅ , σ₆ with ⊎-unassoc σ₆ (⊎-comm σ₄)
... | _ , σ₇ , σ₈ with act σ₅ f σ₇ chs
... | nothing = error {P = _ ✴ _}
... | just (ptr' , (px ×⟨ τ ⟩ chs')) with ⊎-unassoc ptr' σ₈
... | _ , τ₁ , τ₂ with ⊎-unassoc τ₁ τ
... | _ , τ₃ , τ₄ with ⊎-assoc (⊎-comm τ₄) τ₂
... | _ , τ₅ , eureka =
  inj₂ (inj (px ×⟨ ⊎-comm τ₃ ⟩ point) ×⟨ offerᵣ eureka ⟩ lift (channels chs') (⊎-comm τ₅))

receive? : ∀[ Endptr (a ¿ β) ⇒ⱼ State (uncurry Channels) (CVal a ✴ Endptr β) ]
receive? ptr = app (operate (λ i → wandit recvₗ)) ptr ⊎-idˡ

send! : ∀[ Endptr (a ! β) ⇒ CVal a ─✴ⱼ State (uncurry Channels) (Emp ✴ Endptr β) ]
app (send! {a = a} ptr) v σ = app (operate sender) ptr (⊎-comm σ)
  where
    -- this closes over the resource contained in v
    sender : Action (a ! γ) γ Emp _
    app (sender _) l σ =
      let l' = send-into (v ×⟨ σ ⟩ revLink l)
      in inj₂ (empty ×⟨ ⊎-idˡ ⟩ (revLink l'))
