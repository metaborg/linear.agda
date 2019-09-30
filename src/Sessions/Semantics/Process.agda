module Sessions.Semantics.Process where

open import Prelude hiding (_∷ʳ_; lift; Lift)
open import Data.List.Relation.Ternary.Interleaving
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Equality.Propositional
open import Data.List.Properties

open import Relation.Unary
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Morphisms
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Reader

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Commands
open import Relation.Unary.Separation.Monad.Free Cmd δ

-- (α ⇝ β) Φ is the type of a buffer with
-- - internal end of type α
-- - external end of type β
-- - whose values consume Φ
data _⇝_ : SType → SType → Pred SCtx 0ℓ where
  emp  : ∀ {α}   → (α ⇝ α) ε
  cons : ∀ {a α} → ∀[ Val a ✴ ((a ¿ α) ⇝ β)⇒ (α ⇝ β) ]

_⇜_ = flip _⇝_

data Channel : SType → SType → Pred SCtx 0ℓ where
  -- At most one of the endpoints has a buffer.
  -- This is an invariant of binary communication, and does not follow immediately from buffer typings.
  -- The opposite endpoint is typed with the dual of the internal end of the buffer.
  chan : ∀ {α'} → α' ≡ α ⁻¹ → ∀[ (γ ⇜ α') ✴ (α ⇝ β) ⇒ Channel γ β ]

flipm : ∀[ Channel α β  ⇒ Channel β α ]
flipm (chan refl x) = chan (sym dual-involutive) (✴-swap x)

data Chans : SCtx → Pred SCtx 0ℓ where
  nil  : Chans [] []
  cons : ∀ {Φ} → ∀[ Channel α β ✴ Chans Φ ⇒ Chans (α ∷ β ∷ Φ) ]

findChannel : ∀ {x zs ys Φ} → [ x ] ⊎ ys ≣ zs →
              Chans zs Φ →
              ∃₂ λ y ys' → [ y ] ⊎ ys' ≣ ys × (Channel x y ✴ Chans ys') Φ
findChannel (consˡ τ) (cons (c ×⟨ σ ⟩ chs)) with ⊎-id⁻ˡ τ
... | refl = -, -, ⊎-∙ , c ×⟨ σ ⟩ chs
findChannel (consʳ (consˡ τ)) (cons (c ×⟨ σ₁ ⟩ chs)) with ⊎-id⁻ˡ τ
... | refl = -, -, ⊎-∙ , flipm c ×⟨ σ₁ ⟩ chs
findChannel (consʳ (consʳ snd₁)) (cons (c₁ ×⟨ σ₁ ⟩ chs)) with findChannel snd₁ chs
... | _ , _ , τ , c₂ ×⟨ σ ⟩ chs' =
  let _ , σ₂ , σ₃ = ⊎-assoc σ (⊎-comm σ₁)
  in -, -, ⊎-∙ᵣ τ , c₂ ×⟨ σ₂ ⟩ cons (c₁ ×⟨ ⊎-comm σ₃ ⟩ chs') 

-- we are constructing a relative monad over the market resource morphism
open import Relation.Unary.Separation.Monad.State (uncurry Chans)

newChannel : ∀ α → ε[ State (Just α ✴ Just (α ⁻¹)) ]
app (newChannel α) (lift chs σ₂) (offerᵣ σ₁) =
  inj (refl ×⟨ ⊎-comm ⊎-∙ ⟩ refl)
    ×⟨ offerᵣ (⊎-∙ₗ σ₁) ⟩
  lift (cons (chan refl (emp ×⟨ ⊎-idˡ ⟩ emp) ×⟨ ⊎-idˡ ⟩ chs)) (⊎-∙ᵣ σ₂)

Message? : Type → SType → Pred SCtx _
Message? a β = Val a ✴ Just β ∪ Just (a ¿ β)

pop? : ∀ {γ} → ∀[ (b ¿ γ) ⇜ α ⇒ (Emp ∪ Val b ✴ (α ⇝ γ)) ]
pop? emp       = inj₁ empty
pop? (cons vs) = inj₂ (tailor vs)
  where
    tailor : ∀[ Val a ✴ ((a ¿ β) ⇝ (b ¿ γ)) ⇒ Val b ✴ (β ⇝ γ) ]
    tailor (v ×⟨ σ ⟩ emp) = v ×⟨ σ ⟩ emp
    tailor (v ×⟨ σ ⟩ cons vs) with tailor vs
    ... | (w ×⟨ σ' ⟩ vs') =
      let _ , σ₂ , σ₃ = ⊎-assoc σ' (⊎-comm σ)
      in w ×⟨ σ₂ ⟩ cons (v ×⟨ ⊎-comm σ₃ ⟩ vs')

read? : ∀ {γ} → ∀[ Channel (b ¿ γ) α ⇒ (Channel (b ¿ γ) α ∪ (Val b ✴ Channel γ α)) ]
read? c@(chan eq (bₗ ×⟨ σ ⟩ bᵣ)) with pop? bₗ
... | inj₁ empty = inj₁ c
... | inj₂ (v ×⟨ σ₁ ⟩ bₗ') =
  let _ , σ₂ , σ₃ = ⊎-assoc σ₁ σ
  in inj₂ (v ×⟨ σ₂ ⟩ (chan eq (bₗ' ×⟨ σ₃ ⟩ bᵣ)))

receive? : ∀ {α} → ∀[ Just (b ¿ α) ⇒ⱼ State (Message? b α) ]
app (receive? refl) (lift chs σ₂) (offerᵣ σ₁) with ⊎-assoc σ₁ (⊎-comm σ₂)
... | _ , σ₃ , σ₄ with findChannel σ₃ chs
... | _ , _ , σ₅ , c ×⟨ σ₆ ⟩ chs' with read? c
... | z = {!!}
-- ... | _ , _ , _ , (consʳ lr) , σ₅ , ch ×⟨ σ₆ ⟩ chs' = {!!}
-- ... | _ , _ , _ , (consˡ lr) , σ₅ , bufferᵣ eq b ×⟨ σ₆ ⟩ chs' with ⊎-id⁻ˡ lr
-- ... | refl = {!!}

-- ... | _ , _ , τ₁ , bufferₗ refl b ×⟨ σ₆ ⟩ chs' with pop? b
-- ... | inj₁ empty =
--   -- if the buffer is empty, we return to the status quo
--   inj (inj₂ refl) ×⟨ offerᵣ σ₁ ⟩ lift chs σ₂
-- ... | inj₂ (v ×⟨ σ₇ ⟩ b') =
--   let _ , σ₈ , σ₉ = ⊎-assoc σ₇ σ₆ in
--   inj (inj₁ (v ×⟨ ⊎-comm ⊎-∙ ⟩ refl))
--     ×⟨ offerᵣ (consˡ {!!}) ⟩ -- σ₈ σ₄ τ₁
--   lift (cons refl (bufferₗ refl b' ×⟨ σ₉ ⟩ chs')) (consʳ (consʳ {!!}))



-- app (pop? refl) (lift chs σ₂) (offerᵣ σ₁) with ⊎-assoc σ₁ (⊎-comm σ₂)

-- app (pop? refl) (lift (cons refl (bufferᵣ b ×⟨ σ₅ ⟩ chs)) σ₂) (offerᵣ σ₁) | _ , consʳ σ₃ , σ₄ = {!!}

-- app (pop? refl) (lift (IsUnitalSep.cons x (bufferᵣ x₁ RawSep.×⟨ sep₁ ⟩ qx)) σ₂) (offerᵣ σ₁) | _ , _∷ˡ_ {cs = x₂ ∷ cs} refl σ₃ , σ₄ = {!x!}

-- -- pattern matching on chs and σ₃ will tell us where to go
-- app (pop? refl) (lift emp σ₂) (offerᵣ σ₁) | _ , () , σ₄

-- app (pop? refl) (lift (cons (ch ×⟨ consˡ fst₁ , snd₁ ⟩ chs)) σ₂) (offerᵣ σ₁) | _ , consˡ σ₃ , σ₄ = {!!}
-- app (pop? refl) (lift (cons (ch ×⟨ consʳ fst₁ , snd₁ ⟩ chs)) σ₂) (offerᵣ σ₁) | _ , consˡ σ₃ , σ₄ = {!!}

-- app (pop? refl) (lift (cons (px ×⟨ sep₁ ⟩ qx)) σ₂) (offerᵣ σ₁) | _ , consʳ σ₃ , σ₄ = {!!}

-- | Threads are clients

Thread : Type → Pred SCtx 0ℓ
Thread a = Free (Val a)

Pool : Pred SCtx 0ℓ
Pool = Bigstar (λ Φ → ∃ λ a → Thread a Φ)

-- -- | The server state

-- open Morphism (market SCtx)
-- open Monads (market SCtx)
-- open Reader (market SCtx) Val (State {V = {!Link!}})
--   renaming (Reader to M)
-- -- open StateOps {V = ?} unit unit (λ where unit → refl)

-- State : fPred
-- State = Links ✴ ○ Pool

-- -- | The monotone state monad

-- M : fPred → fPred
-- M P = State ==✴ State ✴ P

-- runM : ∀ {P} → ∀[ (State ✴ M P) ==✴ (State ✴ P) ]
-- runM = {!!}

-- return : ∀ {P} → ∀[ P ⇒ M P ]
-- return px st σ₁ σ₂ = -, -, σ₂ , st ×⟨ ⊎-comm σ₁ ⟩ px

-- join : ∀ {P} → ∀[ M (M P) ⇒ M P ]
-- join c st σ = ⤇-bind (apply ∘ ✴-swap) (apply (c ×⟨ σ ⟩ st))
--   where open Update

-- -- external map
-- mmap : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ M P ⇒ M Q ]
-- mmap f c st σ = ⤇-map ⟨ id ⟨✴⟩ f ⟩ (apply (c ×⟨ σ ⟩ st))
--   where open Update

-- -- internal bind - I think?
-- bind : ∀ {P Q} → ∀[ (P ─✴ M Q) ⇒ (M P ─✴ M Q) ]
-- bind f mp σ₁ μ₁ σ₂ σ₃             with ⊎-assoc σ₁ σ₂
-- ... | _ , σ₄ , σ₅                 with ⊎-assoc (⊎-comm σ₄) σ₃
-- ... | _ , σ₆ , σ₇                 with mp μ₁ σ₅ σ₆ -- m specifies the frame for the update
-- ... | _ , _ , σ₈ , μ₂ ×⟨ σ₉ ⟩ px  with ⊎-assoc σ₉ σ₈
-- ... | _ , p' , q'                 with resplit σ₇ (⊎-comm σ₉) (⊎-comm σ₈)
-- ... | _ , _ , τ₁ , τ₂ , τ₃        with ⊎-unassoc τ₃ (⊎-comm τ₂)
-- ... | _ , τ₄ , τ₅                 = f px τ₁ μ₂ τ₄ τ₅ 

-- -- open Update
-- -- bind'' : ∀ {P Q} → ∀[ (P ─✴ M Q) ⇒ (M P ─✴ M Q) ]
-- -- bind'' f mp σ₁ μ₁ σ₂ σ₃ with ⊎-assoc σ₁ σ₂
-- -- ... | _ , σ₄ , σ₅ with ⊎-assoc (⊎-comm σ₅) σ₃
-- -- ... | _ , σ₆ , σ₇ with apply (runM ×⟨ ⊎-comm σ₇ ⟩ (μ₁ ×⟨ ⊎-comm σ₄ ⟩ mp))
-- -- ... | ⤇μ✴px with ⤇-map (λ μ✴px → apply ((✴-curry f) ×⟨ {!!} ⟩ (✴-swap μ✴px))) ⤇μ✴px
-- -- ... | ⤇⤇μ✴qx = {!⤇-join ⤇⤇μ✴qx!}

-- -- internal map
-- imap : ∀ {P Q} → ∀[ (P ─✴ Q) ⇒ (M P ─✴ M Q) ]
-- imap f = bind λ px σ → return (f px σ)

-- syntax bind f p s = p ⟪ s ⟫= f

-- putThread : ∀ {a} → ∀[ ○ (Thread a) ⇒ M Emp ]
-- putThread th = {!!}

-- -- | Creating a new channel, returning two compatible endpoints and updated links

-- -- observations
-- --    * lot of trouble/duplication from the distinction between ∀[ _ ⇒ _ ] vs wands
-- --    * because wands take two arguments, rather than being curried, we cannot use normal function composition

-- newChannel : ∀ α → ε[ M (○ (Just α ✴ Just (α ⁻¹))) ]
-- newChannel α μ =
--   ⤇-map (⟨ ✴-swap ⟨✴⟩ id ⟩ ∘ ✴-assocₗ ∘ ✴-rotateᵣ ∘ ✴-assocᵣ)
--   ∘ ⤇-&
--   ∘ both (helper α ×⟨ neither (⊎-identityˡ refl) ⟩ ○-map ─[id]) μ

--   where
--     open Update

--     helper : ∀ α → ε[ Links ==✴ Links ✴ ○ (Just α ✴ Just (α ⁻¹)) ]
--     helper α (lift ls) (on-right x le) (on-left au z≤Φ₁) rewrite ⊎-identity⁻ʳ x =
--       -,
--       -, on-left (⊎-∙ₗ au) (≤-∙ z≤Φ₁)
--       ,  lift (cons ((newLink α) ×⟨ ⊎-∙ , ⊎-identityˡ refl ⟩ ls))
--            ×⟨ on-left (⊎-comm ⊎-∙) (≤-∙ le) ⟩
--          frag (refl ×⟨ ⊎-∙ ⟩ refl)

-- do-send : ∀ {a α} → ∀[ ○ (Just (a ! α) ✴ Val a) ⇒ M (○ (Just (α .force))) ]
-- do-send = {!!}

-- -- a receive might be blocked by the lack of messages in the buffer,
-- -- in which case you will get an unmodified channel pointer back.
-- do-receive : ∀ {a α} → ∀[ ○ (Just (a ¿ α)) ⇒ M (○ ((Just (α .force) ✴ Val a) ∪ Just (a ¿ α))) ]
-- do-receive = {!!}

-- -- | Given a closure and a endpointer, fork of a computation
-- do-fork : ∀[ ○ (Closure (chan α) b ✴ Just α) ─✴ M Emp ]
-- do-fork = {!!}

-- step : ∀[ ○ (Thread a) ⇒ M (○ (Thread a ∪ Val a)) ]

-- step (frag (pure val)) =
--   return (frag (inj₂ val))

-- step (frag (impure (send x ×⟨ σ₀ ⟩ κ))) =
--   do-send (frag x) ⟪ neither (⊎-comm σ₀) ⟫= λ where
--     (frag ch) (neither σ) → return (frag (inj₁ (κ ch σ)))

-- step (frag thread@(impure (receive ch ×⟨ σ₀ ⟩ κ))) =
--   do-receive (frag ch) ⟪ neither (⊎-comm σ₀) ⟫= λ where
--     -- no value in the buffer; reschedule
--     (frag (inj₂ ch))   (neither σ) → return (frag (inj₁ (impure (receive ch ×⟨ ⊎-comm σ ⟩ κ))))
--     -- received a value from the buffer
--     (frag (inj₁ ch✴v)) (neither σ) → return (frag (inj₁ (κ ch✴v σ)))
    
-- step (frag (impure (close x ×⟨ σ ⟩ qx))) = {!!}

-- step (frag (impure (fork x  ×⟨ σ ⟩ qx))) = {!!}
