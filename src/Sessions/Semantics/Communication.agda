module Sessions.Semantics.Communication where

open import Prelude
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

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr
open import Sessions.Semantics.Commands
open import Sessions.Semantics.Runtime


{- A specification of the update we are performing -}
_≔_ : ∀ {x} {ys} {zs} → [ endp x ] ⊎ ys ≣ zs →
             SType → RCtx
_≔_ {zs = x ∷ zs}         (to-right s) α  = x ∷ s ≔ α
_≔_ {zs = chan l r ∷ zs}  (divide lr s) α = chan α r ∷ zs
_≔_ {zs = chan l r ∷ zs}  (divide rl s) α = chan l α ∷ zs
_≔_ {zs = .(endp _) ∷ zs} (to-left s) α   = endp α ∷ zs

{- Type of actions on a link -}
private
  Action : ∀ (from to : SType) → Pt RCtx 0ℓ
  Action from to P Φ = ∀ {τ} → (end : End from τ) → (Channel τ ─✴ Err (P ✴ Channel (end ≔ₑ to))) Φ

module _ where
  open Monads.Monad {{j = id-morph {A = RCtx}}} err-monad
  open Monads using (str)

  {- Takes an endpointer and the channel list and updates it using a link action -}
  act : ∀ {P α xs ds} →
        (ptr : [ endp α ] ⊎ ds ≣ xs) →
        ∀[ Action α β P
           ⇒ Channels' xs
           ─✴ Err (Empty ([ endp β ] ⊎ ds ≣ (ptr ≔ β)) ✴ P ✴ Channels' (ptr ≔ β)) ]

  -- the pointer points to a channel where one end is already closed
  app (act {xs = x ∷ xs} (to-left ptr) f) (ch :⟨ τ ⟩: chs) σ with ⊎-unassoc σ τ
  ... | _ , τ₁ , τ₂ = do
    px ×⟨ τ₄ ⟩ (ch' ×⟨ τ₅ ⟩ chs) ← mapM (app (str chs) (app (f (-, to-left [])) ch τ₁) (⊎-comm τ₂)) ✴-assocᵣ
    return (emp (to-left ptr) ×⟨ ⊎-idˡ ⟩ px ×⟨ τ₄ ⟩ cons (ch' ×⟨ τ₅ ⟩ chs))

  -- the pointer points to the left side of a channel in the state
  app (act {xs = x ∷ xs} (divide lr ptr) f) (ch :⟨ τ ⟩: chs) σ with ⊎-unassoc σ τ
  ... | _ , τ₂ , τ₃ = do
    px ×⟨ τ₄ ⟩ chs ← mapM (app (str chs) (app (f (ending lr)) ch τ₂) (⊎-comm τ₃)) ✴-assocᵣ
    return (emp (divide lr ptr) ×⟨ ⊎-idˡ ⟩ px ×⟨ τ₄ ⟩ cons chs)

  -- the pointer points to the right side of a channel in the state
  app (act {xs = x ∷ xs} (divide rl ptr) f) (ch :⟨ τ ⟩: chs) σ with ⊎-unassoc σ τ
  ... | _ , τ₂ , τ₃ = do
    px ×⟨ τ₄ ⟩ (ch' ×⟨ τ₅ ⟩ chs) ← mapM (app (str chs) (app (f (ending rl)) ch τ₂) (⊎-comm τ₃)) ✴-assocᵣ
    return (emp (divide rl ptr) ×⟨ ⊎-idˡ ⟩ px ×⟨ τ₄ ⟩ cons (ch' ×⟨ τ₅ ⟩ chs))

  -- the pointer points to some channel further down the list
  app (act {xs = x ∷ xs} (to-right ptr) f) (ch :⟨ τ ⟩: chs) σ with ⊎-unassoc σ (⊎-comm τ)
  ... | _ , τ₁ , τ₂ = do
    emp ptr ×⟨ τ₃ ⟩ rhs ← mapM (app (str ch) (app (act ptr f) chs τ₁) (⊎-comm τ₂)) ✴-assocᵣ
    let px ×⟨ τ₄ ⟩ chs' = ✴-assocᵣ rhs
    return (emp (to-right ptr) ×⟨ τ₃ ⟩ (px ×⟨ τ₄ ⟩ cons (✴-swap chs')))

module _ where
  open StateTransformer {C = RCtx} Err
  open Monads.Monad (state-monad {St = Channels})

  {- Updating a single link based on a pointer to one of its endpoints -}
  operate : ∀ {P} → ∀[ Action α β P ⇒ Endptr α ─✴ⱼ State (Channels) (P ✴ Endptr β) ]
  app (app (operate f) refl σ₁) (lift chs k) (offerᵣ σ₂) with ⊎-assoc σ₂ k
  ... | _ , σ₃ , σ₄ with ⊎-assoc (⊎-comm σ₁) σ₃
  ... | _ , σ₅ , σ₆ with ⊎-unassoc σ₆ (⊎-comm σ₄)
  ... | _ , σ₇ , σ₈ with app (act σ₅ f) chs σ₇
  ... | error = error
  ... | partial (inj₂ (emp ptr' ×⟨ σ ⟩ (px ×⟨ τ ⟩ chs'))) with ⊎-id⁻ˡ σ
  ... | refl with ⊎-unassoc ptr' σ₈
  ... | _ , τ₁ , τ₂ with ⊎-unassoc τ₁ τ
  ... | _ , τ₃ , τ₄ with ⊎-assoc (⊎-comm τ₄) τ₂
  ... | _ , τ₅ , eureka =
    partial (inj₂ (inj (px ×⟨ ⊎-comm τ₃ ⟩ refl) ×⟨ offerᵣ eureka ⟩ lift chs' (⊎-comm τ₅)))

  {- Getting a value from a ready-to-receive endpoint -}
  receive? : ∀[ Endptr (a ¿ β) ⇒ⱼ State Channels (Val a ✴ Endptr β) ]
  receive? ptr = app (operate (λ end → wandit (chan-receive end))) ptr ⊎-idˡ

  {- Putting a value in a ready-to-send endpoint -}
  send! : ∀[ Endptr (a ! β) ⇒ Val a ─✴ⱼ State Channels (Endptr β) ]
  app (send! {a = a} ptr) v σ = do
    empty ×⟨ σ ⟩ ptr ← app (operate sender) ptr (⊎-comm σ)
    case ⊎-id⁻ˡ σ of λ where
      refl → return ptr
    where
      sender : Action (a ! γ) γ Emp _
      app (sender e) ch σ =
        let ch' = app (chan-send e ch) v (⊎-comm σ) 
        in ✓ (empty ×⟨ ⊎-idˡ ⟩ ch')

module _ where
  open StateMonad {C = RCtx}

  newChan : ε[ State Channels (Endptr α ✴ Endptr (α ⁻¹)) ]
  app newChan (lift chs k) σ with ⊎-id⁻ˡ σ
  ... | refl = (
   (inj (refl ×⟨ divide lr ⊎-idˡ ⟩ refl))
      ×⟨ offerᵣ ⊎-∙ ⟩
   lift (cons (emptyChannel ×⟨ ⊎-idˡ ⟩ chs)) (⊎-∙ₗ k)) 

  closeChan : ∀[ Endptr end ⇒ⱼ State Channels Emp ]
  closeChan ptr = {!!}
