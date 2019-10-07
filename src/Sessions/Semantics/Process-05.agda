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

  the-update : ∀ {x} {ys} {zs : List (SType × SType)} → [ endp x ] ⊎ ys ≣ ⟦ zs ⟧ →
               ∀ y → ∃ λ zs' → [ endp y ] ⊎ ys ≣ ⟦ zs' ⟧
  the-update {zs = []} ()
  the-update {zs = (_ , r) ∷ zs} (divide lr s) α = (α , r) ∷ zs , divide lr s
  the-update {zs = (l , _) ∷ zs} (divide rl s) α = (l , α) ∷ zs , divide rl s
  the-update {zs = x ∷ zs} (to-right s) α with the-update s α
  ... | zs' , s' = x ∷ zs' , to-right s'

  -- {- Takes an endpointer and its providing channel and updates it using a link action -}
  act : ∀ {P α cs xs c₁ c₂ ds} →
        (ptr : [ endp α ] ⊎ ds ≣ ⟦ xs ⟧) → (Action α β P) c₁ → c₁ ⊎ c₂ ≣ cs →
        let xs' = proj₁ (the-update ptr β) in
        Channels' xs c₂ → Maybe ([ endp β ] ⊎ ds ≣ ⟦ xs' ⟧ × (P ✴ Channels' xs') cs)

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

  -- {- The form of the separation evidence heavily depends on where exactly the endpoint α can be found... -}
  -- rewrite-frame : ∀ {fr₁ Φᵢ fr₂ Φ Φₗ Φᵣ : RCtx} →
  --                 [ endp α ] ⊎ fr₁ ≣ Φ →
  --                 Φᵢ ⊎ fr₂ ≣ Φ →
  --                 Φₗ ⊎ Φᵣ ≣ Φᵢ →
  --                 ∃₂ λ zs ys →
  --                     (zs ⊎ fr₂ ≣ (chan α β ∷ fr₁))
  --                   × ys ⊎ Φᵣ ≣ zs
  --                   × Φₗ ⊎ [ endp β ] ≣ ys

  -- rewrite-frame (to-left σ₁) (to-right σ₂) σ₃ rewrite ⊎-id⁻ˡ σ₁
  --   = -, -, divide rl σ₂ , ⊎-∙ₗ σ₃ , ⊎-comm ⊎-∙
  -- rewrite-frame (to-left σ₁) (to-left σ₂) (to-left σ₃) rewrite ⊎-id⁻ˡ σ₁
  --   = -, -, to-left σ₂ , to-left σ₃ , divide lr ⊎-idʳ
  -- rewrite-frame (to-left σ₁) (to-left σ₂) (to-right σ₃) rewrite ⊎-id⁻ˡ σ₁
  --   = -, -, to-left σ₂ , divide rl σ₃ , ⊎-comm ⊎-∙

  -- rewrite-frame (divide x σ₁) σ₂ σ₃ with ⊎-id⁻ˡ σ₁
  -- ... | refl = {!!} , {!!} , {!!} , {!!} , {!!}
  -- rewrite-frame (to-right σ₁) σ₂ σ₃ = {!!} , {!!} , {!!} , {!!} , {!!}

  -- {- Takes an endpointer and its providing channel and updates it using a link action -}
  -- act : ∀ {P} → ∀[ Π₂ (Action α β P) ⇒ (Endptr α ◑ Ch) ─✴ ⟰? (Π₂ (P ✴ Endptr β) ✴ Ch) ]

  -- app (act (snd f)) (point ◑⟨ divide rl [] ⟩ chan (chan l)) (σ₂ , σ₃) with ⊎-id⁻ˡ σ₂
  -- ... | refl = {!!}

  -- app (act (snd f)) (point ◑⟨ divide lr [] ⟩ chan (chan l)) (σ₂ , σ₃) with ⊎-id⁻ˡ σ₂
  -- ... | refl with app (f _) (revLink l) σ₃
  -- ... | inj₁ tt = ⟰error _
  -- ... | inj₂ (px ×⟨ σ₄ ⟩ l') = complete λ fr →
  --   let _ , _ , τ₁ , τ₂ , τ₃ = rewrite-frame (proj₁ fr) (proj₂ fr) σ₄
  --   in -, -,
  --     (⊎-∙ , τ₁)
  --   , inj₂ ((snd (px ×⟨ τ₃ ⟩ point)) ×⟨ ⊎-idˡ , {!!} ⟩ chan (chan (revLink l')))

  -- opper : ∀ {P} → ∀[ Π₂ (Action α β P) ⇒ (Endptr α ◑ Chs) ─✴ ⟰? ((Π₂ P ✴ (Endptr β ◑ Chs))) ]

  -- -- state cannot be empty because we have a pointer into it
  -- app (opper f) (frag point () nil)

  -- -- the channel we are looking for is at the head of the state
  -- app (opper f) (frag point (divide rl σ₁) (ch :⟨ σ₂ ⟩: chs)) (σ₃ , σ₄) with ⊎-id⁻ˡ σ₁ | ⊎-unassoc σ₄ σ₂
  -- ... | refl | _ , σ₅ , σ₆ = do
  --   {!!}

  -- app (opper f) (frag point (divide lr σ₁) (ch :⟨ σ₂ ⟩: chs)) (σ₃ , σ₄) with ⊎-id⁻ˡ σ₁ | ⊎-unassoc σ₄ σ₂
  -- ... | refl | _ , σ₅ , σ₆ = do
  --   let _ , σ₇ , σ₈ = unspliceᵣ σ₃
  --   (px ×⟨ τ₁ ⟩ (frag point (divide s []) (chan (chan l')))) ×⟨ τ ⟩ chs ← str Chs (app (opperst f) (frag point (divide lr ⊎-idˡ) (chan ch)) (σ₇ , σ₅) ×⟨ σ₈ , σ₆ ⟩ (Idm.inj chs))
  --   let _ , τ₃ , τ₄ = ⊎-assoc τ₁ τ
  --   let _ , τ₅ , τ₆ = ⊎-unassoc ((proj₁ τ₃)) (proj₁ τ₄) 
  --   return (px ×⟨ {!τ₅!} , {!!} ⟩ (frag point (divide s ⊎-idˡ) (cons (chan l' ×⟨ proj₂ τ₄ ⟩ chs))))

  -- -- app (opper f) (frag point (divide s σ₁) (ch :⟨ σ₂ ⟩: chs)) (σ₃ , σ₄) with ⊎-id⁻ˡ σ₁ | ⊎-unassoc σ₄ σ₂
  -- -- ... | refl | _ , σ₅ , σ₆ = do
  -- --   let _ , σ₇ , σ₈ = unspliceᵣ σ₃
  -- --   (px ×⟨ τ₁ ⟩ (frag point (divide lr []) (chan (chan l')))) ×⟨ τ ⟩ chs ← str Chs (app (opperst f) (frag point (divide s ⊎-idˡ) (chan ch)) (σ₇ , σ₅) ×⟨ σ₈ , σ₆ ⟩ (Idm.inj chs))
  -- --     where
  -- --       _ → {!!}
  -- --   let _ , τ₃ , τ₄ = ⊎-assoc τ₁ τ
  -- --   return (px ×⟨ τ₃ ⟩ (frag point ({!!}) (cons (chan l' ×⟨ proj₂ τ₄ ⟩ chs))))

  -- -- recursive case
  -- app (opper (snd f)) (frag point (to-right σ₁)  (ch :⟨ σ₂ ⟩: chs)) (σ₃ , σ₄) with ⊎-id⁻ˡ σ₃ | ⊎-unassoc σ₄ (⊎-comm σ₂)
  -- ... | refl | _ , σ₅ , σ₆ = do
  --   (px ×⟨ τ ⟩ (frag p τ₁ chs)) ×⟨ τ₂ ⟩ chan (chan ch) ← str Ch (app (opper (snd f)) (frag point σ₁ chs) (⊎-idˡ , σ₅) ×⟨ ⊎-∙ᵣ ⊎-idʳ , σ₆ ⟩ Idm.inj (chan ch))
  --   let xs , τ₃ , τ₄ = ⊎-assoc τ τ₂
  --   return (px ×⟨ τ₃ ⟩ frag p {!!} (cons ((chan ch) ×⟨ ⊎-comm (proj₂ τ₄) ⟩ chs)))

  -- open StateTransformer {C = RCtx} Err

  -- operate : ∀ {P} → ∀[ Action α β P ⇒ Endptr α ─✴ⱼ State Chs (P ✴ Endptr β) ]
  -- app (app (operate act) ptr σ₁) μ (offerᵣ σ₂) with ⊎-assoc (⊎-comm σ₁) σ₂
  -- ... | _ , σ₃ , σ₄ = do
  --   let μ₁ = app (absorb ptr) μ (offerᵣ σ₃)
  --   --let μ₂ = app (●-update (lift (opper (snd act)))) μ₁ (offerᵣ σ₄)
  --   {!!}
  --   -- let px   ×⟨ τ₁  ⟩ μ₃ = ○≺●ᵣ μ₂
  --   -- let ptr' ×⟨ τ₂ ⟩ μ₄ = expell μ₃
  --   -- let _ , τ₃ , τ₄ = ⊎-unassoc τ₁ τ₂
  --   -- Err.return {_ ✴ ● _} (jstar⁻ (px ×⟨ τ₃ ⟩ ptr') ×⟨ τ₄ ⟩ μ₄)

{-
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
... | inj₁ _ = error {P = _ ✴ ● _}

-- f'ine
... | inj₂ (px ×⟨ τ₂ ⟩ l') with resplit τ₂ σ₈ σ₉
-- argh, three cases, only splittings differ
-- 1: other endpoint in the frame
... | _ , _ , τ₃ , τ₄ , to-right τ₅  = Err.return {P = _ ✴ ● _} (
      inj (px ×⟨ ⊎-comm ⊎-∙ ⟩ point)
        ×⟨ offerᵣ (⊎-∙ₗ τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (divide lr τ₅))
-- 2: other endpoint in the store
... | _ , _ , to-left τ₃ , τ₄ , to-left τ₅  = Err.return {P = _ ✴ ● _} (
      inj (px ×⟨ divide rl ⊎-idʳ ⟩ point)
        ×⟨ offerᵣ (to-left τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (to-left τ₅))
-- 3: other endpoint in px
... | _ , _ , to-right τ₃ , τ₄ , to-left τ₅  = Err.return {P = _ ✴ ● _} (
      inj (px ×⟨ ⊎-comm ⊎-∙ ⟩ point)
        ×⟨ offerᵣ (divide rl τ₃) ⟩
      lift (cons (chan (revLink l') ×⟨ τ₄ ⟩ chs)) (to-left τ₅))
 
{- found 'm: first channel, left endpoint -}
app (app (operate f) point σ₁) μ@(lift (chan l :⟨ τ ⟩: chs) k) (offerᵣ σ₂)
  | _ , σ₃ , σ₄
  | _ , divide lr σ₅ , σ₆ with ⊎-id⁻ˡ σ₅
... | refl with resplit σ₄ τ σ₆
... | bc , cd , σ₇ , σ₈ , σ₉ with app (f _) l σ₇

-- f'ed
... | inj₁ _ = error {P = _ ✴ ● _}

-- f'ine
... | inj₂ (px ×⟨ τ₂ ⟩ l') with resplit τ₂ σ₈ σ₉
-- argh, three cases, only splittings differ
-- 1: other endpoint in the frame
... | _ , _ , τ₃ , τ₄ , to-right τ₅  = Err.return {P = _ ✴ ● _} (
      inj (px ×⟨ ⊎-comm ⊎-∙ ⟩ point)
        ×⟨ offerᵣ (⊎-∙ₗ τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (divide lr τ₅))
-- 2: other endpoint in the store
... | _ , _ , to-left τ₃ , τ₄ , to-left τ₅  = Err.return {P = _ ✴ ● _} (
      inj (px ×⟨ divide rl ⊎-idʳ ⟩ point)
        ×⟨ offerᵣ (to-left τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (to-left τ₅))
-- 3: other endpoint in px
... | _ , _ , to-right τ₃ , τ₄ , to-left τ₅  = Err.return {P = _ ✴ ● _} (
      inj (px ×⟨ ⊎-comm ⊎-∙ ⟩ point)
        ×⟨ offerᵣ (divide lr τ₃) ⟩
      lift (cons (chan l' ×⟨ τ₄ ⟩ chs)) (to-left τ₅))
-}

-- receive? : ∀[ Endptr (a ¿ β) ⇒ⱼ State Chs (CVal a ✴ Endptr β) ]
-- receive? ptr = app (operate (λ i → wandit recvₗ)) ptr ⊎-idˡ

-- send! : ∀[ Endptr (a ! β) ⇒ CVal a ─✴ⱼ State Chs (Emp ✴ Endptr β) ]
-- app (send! {a = a} ptr) v σ = app (operate sender) ptr (⊎-comm σ)
--   where
--     -- this closes over the resource contained in v
--     sender : Action (a ! γ) γ Emp _
--     app (sender _) l σ =
--       let l' = send-into (v ×⟨ σ ⟩ revLink l)
--       in inj₂ (empty ×⟨ ⊎-idˡ ⟩ (revLink l'))
