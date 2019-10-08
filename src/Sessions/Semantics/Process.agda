module Sessions.Semantics.Process where

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
open import Sessions.Semantics.Runtime hiding (_>>=_; mapM; return)

open import Relation.Unary.Separation.Construct.ListOf Runtype

{- Type of actions on a link -}
private
  Action : SType → SType → Pt RCtx 0ℓ
  Action α β P = ⋂[ γ ∶ _ ] (Link α γ ─✴ Err (P ✴ Link β γ))
  
  jm = id-morph RCtx
  open Monads.Monad {j = jm} err-monad
  open Monads {{ bs = record { Carrier = RCtx } }} jm using (str)
  module Idm = Morphism jm

module _ where

  {- A specification of the update we are performing -}
  _≔_ : ∀ {x} {ys} {zs : List (SType × SType)} → [ endp x ] ⊎ ys ≣ ⟦ zs ⟧ →
               SType → List (SType × SType)
  _≔_ {zs = (_ , r) ∷ zs} (divide lr s) α = (α , r) ∷ zs
  _≔_ {zs = (l , _) ∷ zs} (divide rl s) α = (l , α) ∷ zs
  _≔_ {zs = x ∷ zs}       (to-right s)  α = x ∷ (s ≔ α)

  {- Takes an endpointer and the channel list and updates it using a link action -}
  act : ∀ {P α xs ds} →
        (ptr : [ endp α ] ⊎ ds ≣ ⟦ xs ⟧) →
        ∀[ (Action α β P) ⇒ Channels' xs ─✴ Err (Empty ([ endp β ] ⊎ ds ≣ ⟦ ptr ≔ β ⟧) ✴ P ✴ Channels' (ptr ≔ β)) ]

  app (act {xs = x ∷ xs} (divide lr ptr) f) (l :⟨ τ ⟩: chs) σ with ⊎-unassoc σ τ
  ... | _ , τ₂ , τ₃ = do
    px ×⟨ τ₄ ⟩ chs ← mapM (app (str chs) (app (f _) l τ₂) (⊎-comm τ₃)) ✴-assocᵣ
    return (emp (divide lr ptr) ×⟨ ⊎-idˡ ⟩ px ×⟨ τ₄ ⟩ cons chs)

  app (act {xs = x ∷ xs} (divide rl ptr) f) (l :⟨ τ ⟩: chs) σ with ⊎-unassoc σ τ
  ... | _ , τ₂ , τ₃ = do
    px ×⟨ τ₄ ⟩ (l' ×⟨ τ₅ ⟩ chs) ← mapM (app (str chs) (app (f _) (revLink l) τ₂) (⊎-comm τ₃)) ✴-assocᵣ
    return (emp (divide rl ptr) ×⟨ ⊎-idˡ ⟩ px ×⟨ τ₄ ⟩ cons (revLink l' ×⟨ τ₅ ⟩ chs))

  app (act {xs = x ∷ xs} (to-right ptr) f) (ch :⟨ τ ⟩: chs) σ with ⊎-unassoc σ (⊎-comm τ)
  ... | _ , τ₁ , τ₂ = do
    emp ptr ×⟨ τ₃ ⟩ rhs ← mapM (app (str ch) (app (act ptr f) chs τ₁) (⊎-comm τ₂)) ✴-assocᵣ
    let px ×⟨ τ₄ ⟩ chs' = ✴-assocᵣ rhs
    return (emp (to-right ptr) ×⟨ τ₃ ⟩ (px ×⟨ τ₄ ⟩ cons (✴-swap chs')))

open StateTransformer {C = RCtx} Err

{- Updating a single link based on a pointer to one of its endpoints -}
operate : ∀ {P} → ∀[ Action α β P ⇒ Endptr α ─✴ⱼ State (uncurry Channels) (P ✴ Endptr β) ]
app (app (operate f) point σ₁) (lift (channels chs) k) (offerᵣ σ₂) with ⊎-assoc σ₂ k
... | _ , σ₃ , σ₄ with ⊎-assoc (⊎-comm σ₁) σ₃
... | _ , σ₅ , σ₆ with ⊎-unassoc σ₆ (⊎-comm σ₄)
... | _ , σ₇ , σ₈ with app (act σ₅ f) chs σ₇
... | error = error
... | partial (inj₂ (emp ptr' ×⟨ σ ⟩ (px ×⟨ τ ⟩ chs'))) with ⊎-id⁻ˡ σ
... | refl with ⊎-unassoc ptr' σ₈
... | _ , τ₁ , τ₂ with ⊎-unassoc τ₁ τ
... | _ , τ₃ , τ₄ with ⊎-assoc (⊎-comm τ₄) τ₂
... | _ , τ₅ , eureka =
  partial (inj₂ (inj (px ×⟨ ⊎-comm τ₃ ⟩ point) ×⟨ offerᵣ eureka ⟩ lift (channels chs') (⊎-comm τ₅)))

{- Getting a value from a ready-to-receive endpoint -}
receive? : ∀[ Endptr (a ¿ β) ⇒ⱼ State (uncurry Channels) (CVal a ✴ Endptr β) ]
receive? ptr = app (operate (λ i → wandit recvₗ)) ptr ⊎-idˡ

{- Putting a value in a ready-to-send endpoint -}
send! : ∀[ Endptr (a ! β) ⇒ CVal a ─✴ⱼ State (uncurry Channels) (Emp ✴ Endptr β) ]
app (send! {a = a} ptr) v σ = app (operate sender) ptr (⊎-comm σ)
  where
    -- this closes over the resource contained in v
    sender : Action (a ! γ) γ Emp _
    app (sender _) l σ =
      let l' = send-into (v ×⟨ σ ⟩ revLink l)
      in return (empty ×⟨ ⊎-idˡ ⟩ (revLink l'))
