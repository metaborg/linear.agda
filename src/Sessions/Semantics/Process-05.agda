module Sessions.Semantics.Process-05 where

open import Prelude hiding (_∷ʳ_; lift; Lift)
open import Data.List.Relation.Ternary.Interleaving
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Equality.Propositional 
open import Data.List.Properties
import Data.List as L

open import Relation.Unary hiding (Empty; _∈_)
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Reader

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Commands
-- open import Relation.Unary.Separation.Monad.Free Cmd δ
open import Relation.Unary.Separation.Monad.Error
open import Relation.Unary.Separation.Monad.State

open import Relation.Unary.Separation.Construct.ListOf Runtype

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
recvₗ c@(link refl (emp ×⟨ _ ⟩ _)) = error {P = _ ✴ Link _ _}
recvₗ (link refl (cons (v ×⟨ σ₁ ⟩ bₗ) ×⟨ σ₂ ⟩ bᵣ)) =
  let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
  in inj₂ (v ×⟨ σ₃ ⟩ (link refl (bₗ ×⟨ σ₄ ⟩ bᵣ)))

recvᵣ : ∀[ Link γ (a ¿ β) ⇒ Err (CVal a ✴ Link γ β) ]
recvᵣ l with recvₗ (revLink l)
... | inj₁ _ = error {P = _ ✴ Link _ _}
... | inj₂ (v ×⟨ σ ⟩ l') = inj₂ (v ×⟨ σ ⟩ revLink l')

data Channel : Runtype → Pred RCtx 0ℓ where
  chan : ∀[ Link α γ ⇒ Channel (chan α γ) ]

Chs : Pred (RCtx × RCtx) 0ℓ
Chs = uncurry (Allstar Channel)

-- merge : ∀[ Chs ⇒ Chs ─✴ Chs ]
-- app (merge chs₁) (cons (ch ×⟨ σ₂ ⟩ chs₂)) (consʳ σ₁ , σ₃) =
--   let _ , σ₄ , σ₅ = ⊎-assoc σ₂ (⊎-comm σ₃) in cons (ch ×⟨ σ₄ ⟩ app (merge chs₁) chs₂ (σ₁ , ⊎-comm σ₅))
-- app (merge (cons (ch ×⟨ σ₂ ⟩ chs₁))) chs₂@(cons _) (consˡ σ₁ , σ₃) =
--   let _ , σ₄ , σ₅ = ⊎-assoc σ₂ σ₃ in cons (ch ×⟨ σ₄ ⟩ app (merge chs₁) chs₂ (σ₁ , σ₅))
-- app (merge chs₁@(cons _)) nil (consˡ σ₁ , σ₃) with ⊎-id⁻ʳ σ₁ | ⊎-id⁻ʳ σ₃
-- ... | refl | refl = chs₁
-- app (merge nil) nil ([] , []) = nil

-- End : SType → Pred RCtx _
-- End = λ α → ⋃[ β ∶ _ ] (Channel (chan α β) ∪ Channel (chan β α))

emptyChannel : ε[ Channel (chan α (α ⁻¹)) ]
emptyChannel = chan (link refl (emp ×⟨ ⊎-∙ ⟩ emp))

newChan : ε[ State Chs (Endptr α ✴ Endptr (α ⁻¹)) ]
app newChan (lift chs k) σ with ⊎-id⁻ˡ σ
... | refl =
  (inj (point ×⟨ divide lr ⊎-idˡ ⟩ point))
    ×⟨ offerᵣ ⊎-∙ ⟩
  lift (cons (emptyChannel ×⟨ ⊎-idˡ ⟩ chs)) (⊎-∙ₗ k)

-- TODO the f is really a heterogenous, errorful state operation
operate : ∀ {P} → ∀[ ⋂[ γ ∶ _ ] (Link α γ ─✴ Err (P ✴ Link β γ)) ⇒ Endptr α ─✴ⱼ State Chs (Err (P ✴ Endptr β)) ]

-- clearly the state cannot be empty
app (app (operate f) point σ₁) (lift nil []) (offerᵣ σ₂) with ⊎-ε σ₂
app (app (operate f) point ()) _ _ | refl , refl

app (app (operate f) point σ₁) μ@(lift (chan l :⟨ τ ⟩: chs) k) (offerᵣ σ₂) with ⊎-assoc (⊎-comm σ₁) σ₂

{- recursive case -}
... | _ , σ₃ , σ₄ with ⊎-assoc σ₃ k
... | _ , to-right σ₅ , σ₆ = {!operate!}
  -- where
  -- operate' : x ∈ xs → Allstar xs ─✴ Allstar ()
  -- chs : Allstar Channel xs Φᵣ  -- the tail
  -- σ₅  : [ endp α ] ⊎ ys ≣ xs   -- the 'ptr'

{- found 'm: right channel, left endpoint -}
app (app (operate f) point σ₁) μ@(lift (chan l :⟨ τ ⟩: chs) k) (offerᵣ σ₂)
  | _ , σ₃ , σ₄
  | _ , divide rl σ₅ , σ₆ with ⊎-id⁻ˡ σ₅
... | refl with resplit σ₄ τ σ₆
... | bc , cd , σ₇ , σ₈ , σ₉ with app (f _) (revLink l) σ₇

-- f'ed
... | inj₁ _ = inj (inj₁ tt) ×⟨ offerᵣ σ₂ ⟩ μ

-- f'ine
... | inj₂ (px ×⟨ τ₂ ⟩ l') with resplit τ₂ σ₈ σ₉
-- argh, three cases, only splittings differ
-- 1: other endpoint in the frame
... | _ , _ , τ₃ , τ₄ , to-right τ₅  = 
      inj (inj₂ (px ×⟨ ⊎-comm ⊎-∙ ⟩ point))
        ×⟨ offerᵣ (⊎-∙ₗ τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (divide lr τ₅)
-- 2: other endpoint in the store
... | _ , _ , to-left τ₃ , τ₄ , to-left τ₅  =
      inj (inj₂ (px ×⟨ divide rl ⊎-idʳ ⟩ point))
        ×⟨ offerᵣ (to-left τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (to-left τ₅)
-- 3: other endpoint in px
... | _ , _ , to-right τ₃ , τ₄ , to-left τ₅  =
      inj (inj₂ (px ×⟨ ⊎-comm ⊎-∙ ⟩ point))
        ×⟨ offerᵣ (divide rl τ₃) ⟩
      lift (cons (chan (revLink l') ×⟨ τ₄ ⟩ chs)) (to-left τ₅)
 
{- found 'm: first channel, left endpoint -}
app (app (operate f) point σ₁) μ@(lift (chan l :⟨ τ ⟩: chs) k) (offerᵣ σ₂)
  | _ , σ₃ , σ₄
  | _ , divide lr σ₅ , σ₆ with ⊎-id⁻ˡ σ₅
... | refl with resplit σ₄ τ σ₆
... | bc , cd , σ₇ , σ₈ , σ₉ with app (f _) l σ₇

-- f'ed
... | inj₁ _ = inj (inj₁ tt) ×⟨ offerᵣ σ₂ ⟩ μ

-- f'ine
... | inj₂ (px ×⟨ τ₂ ⟩ l') with resplit τ₂ σ₈ σ₉
-- argh, three cases, only splittings differ
-- 1: other endpoint in the frame
... | _ , _ , τ₃ , τ₄ , to-right τ₅  = 
      inj (inj₂ (px ×⟨ ⊎-comm ⊎-∙ ⟩ point))
        ×⟨ offerᵣ (⊎-∙ₗ τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (divide lr τ₅)
-- 2: other endpoint in the store
... | _ , _ , to-left τ₃ , τ₄ , to-left τ₅  =
      inj (inj₂ (px ×⟨ divide rl ⊎-idʳ ⟩ point))
        ×⟨ offerᵣ (to-left τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (to-left τ₅)
-- 3: other endpoint in px
... | _ , _ , to-right τ₃ , τ₄ , to-left τ₅  =
      inj (inj₂ (px ×⟨ ⊎-comm ⊎-∙ ⟩ point))
        ×⟨ offerᵣ (divide lr τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (to-left τ₅)

receive? : ∀[ Endptr (a ¿ β) ⇒ⱼ State Chs (Err (CVal a ✴ Endptr β)) ]
receive? ptr = app (operate (λ i → wandit recvₗ)) ptr ⊎-idˡ

send! : ∀[ Endptr (a ! β) ⇒ CVal a ─✴ⱼ State Chs (Err (Emp ✴ Endptr β)) ]
app (send! {a = a} ptr) v σ = app (operate sender) ptr (⊎-comm σ)
  where
    -- this closes over the resource contained in v
    sender : ∀ γ → (Link (a ! β) γ ─✴ Err (Emp ✴ Link β γ)) _
    app (sender _) l σ =
      let l' = send-into (v ×⟨ σ ⟩ revLink l)
      in inj₂ (empty ×⟨ ⊎-idˡ ⟩ (revLink l'))
