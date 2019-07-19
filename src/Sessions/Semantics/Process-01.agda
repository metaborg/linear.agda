module Sessions.Semantics.Process-01 where

open import Prelude hiding (_∷ʳ_; lift; Lift)
open import Data.Unit
open import Data.List.Relation.Ternary.Interleaving
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Equality.Propositional

open import Relation.Unary
open import Relation.Unary.Separation.Construct.Product

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Expr-01 using (receive; send; close; fork)
open import Sessions.Semantics.Expr-02

-- A framed predicate
open import Relation.Unary.Separation.Construct.Auth SCtx
fPred = Pred Auth 0ℓ

data Lift (P : Pred (SCtx × SCtx) 0ℓ) : fPred where
  lift : ∀ {Φ₁ Φ₂} → P (Φ₁ , Φ₂) → Lift P (Φ₁ ◐ Φ₂)

instance
  auth-raw : RawSep Auth
  auth-raw = auth-raw-sep

-- | The channel buffers and links (predicates over `SCtx × SCtx`)
-- The left context is the 'authorative' part,
-- and the right context is the 'client' part

data _⇝_ : SType ∞ → SType ∞ → Pred (SCtx × SCtx) 0ℓ where
  emp  : ∀ {α}   → (α ⇝ α) ([ α ] , ε)
  snoc : ∀ {a α} → ε[ (Val a ∘ proj₂) ─✴ ((a ¿ α) ⇝ β) ─✴ (α .force ⇝ β) ]

_⇜_ = flip _⇝_

data Link : Pred (SCtx × SCtx) 0ℓ where
  link : ∀[ α ⇜ β ✴ (β ⁻¹ ⇝ γ) ⇒ Link ]

newLink : ∀ α → Link (α ∷ α ⁻¹ ∷ [] , ε)
newLink α = link $ emp ×⟨ consˡ (consʳ []) , ⊎-identityˡ refl ⟩ emp

Links : Pred Auth 0ℓ
Links = Lift (Bigstar Link)

-- | Threads are clients (predicates over `SCtx`)

Thread : Type ∞ → Pred SCtx 0ℓ
Thread a = F (Val a)

Pool : Pred SCtx 0ℓ
Pool = Bigstar (λ Φ → ∃ λ a → Thread a Φ)

-- | The server state

State : fPred
State = Links ✴ ○ Pool

-- | The monotone state monad

M : fPred → fPred
M P = State ==✴ State ✴ P

runM : ∀ {P} → ∀[ (State ✴ M P) ==✴ (State ✴ P) ]
runM = {!!}

return : ∀ {P} → ∀[ P ⇒ M P ]
return px st σ₁ σ₂ = -, -, σ₂ , st ×⟨ ⊎-comm σ₁ ⟩ px

join : ∀ {P} → ∀[ M (M P) ⇒ M P ]
join c st σ = ⤇-bind (apply ∘ ✴-swap) (apply (c ×⟨ σ ⟩ st))
  where open Update

-- external map
mmap : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ M P ⇒ M Q ]
mmap f c st σ = ⤇-map ⟨ id ⟨✴⟩ f ⟩ (apply (c ×⟨ σ ⟩ st))
  where open Update

-- internal bind - I think?
bind : ∀ {P Q} → ∀[ (P ─✴ M Q) ⇒ (M P ─✴ M Q) ]
bind f mp σ₁ μ₁ σ₂ σ₃             with ⊎-assoc σ₁ σ₂
... | _ , σ₄ , σ₅                 with ⊎-assoc (⊎-comm σ₄) σ₃
... | _ , σ₆ , σ₇                 with mp μ₁ σ₅ σ₆ -- m specifies the frame for the update
... | _ , _ , σ₈ , μ₂ ×⟨ σ₉ ⟩ px  with ⊎-assoc σ₉ σ₈
... | _ , p' , q'                 with resplit σ₇ (⊎-comm σ₉) (⊎-comm σ₈)
... | _ , _ , τ₁ , τ₂ , τ₃        with ⊎-unassoc τ₃ (⊎-comm τ₂)
... | _ , τ₄ , τ₅                 = f px τ₁ μ₂ τ₄ τ₅ 

-- open Update
-- bind'' : ∀ {P Q} → ∀[ (P ─✴ M Q) ⇒ (M P ─✴ M Q) ]
-- bind'' f mp σ₁ μ₁ σ₂ σ₃ with ⊎-assoc σ₁ σ₂
-- ... | _ , σ₄ , σ₅ with ⊎-assoc (⊎-comm σ₅) σ₃
-- ... | _ , σ₆ , σ₇ with apply (runM ×⟨ ⊎-comm σ₇ ⟩ (μ₁ ×⟨ ⊎-comm σ₄ ⟩ mp))
-- ... | ⤇μ✴px with ⤇-map (λ μ✴px → apply ((✴-curry f) ×⟨ {!!} ⟩ (✴-swap μ✴px))) ⤇μ✴px
-- ... | ⤇⤇μ✴qx = {!⤇-join ⤇⤇μ✴qx!}

-- internal map
imap : ∀ {P Q} → ∀[ (P ─✴ Q) ⇒ (M P ─✴ M Q) ]
imap f = bind λ px σ → return (f px σ)

syntax bind f p s = p ⟪ s ⟫= f

putThread : ∀ {a} → ∀[ ○ (Thread a) ⇒ M Emp ]
putThread th = {!!}

-- | Creating a new channel, returning two compatible endpoints and updated links

-- observations
--    * lot of trouble/duplication from the distinction between ∀[ _ ⇒ _ ] vs wands
--    * because wands take two arguments, rather than being curried, we cannot use normal function composition

newChannel : ∀ α → ε[ M (○ (Just α ✴ Just (α ⁻¹))) ]
newChannel α μ =
  ⤇-map (⟨ ✴-swap ⟨✴⟩ id ⟩ ∘ ✴-assocₗ ∘ ✴-rotateᵣ ∘ ✴-assocᵣ)
  ∘ ⤇-&
  ∘ both (helper α ×⟨ neither (⊎-identityˡ refl) ⟩ ○-map ─[id]) μ

  where
    open Update

    helper : ∀ α → ε[ Links ==✴ Links ✴ ○ (Just α ✴ Just (α ⁻¹)) ]
    helper α (lift ls) (on-right x le) (on-left au z≤Φ₁) rewrite ⊎-identity⁻ʳ x =
      -,
      -, on-left (⊎-∙ₗ au) (≤-∙ z≤Φ₁)
      ,  lift (cons ((newLink α) ×⟨ ⊎-∙ , ⊎-identityˡ refl ⟩ ls))
           ×⟨ on-left (⊎-comm ⊎-∙) (≤-∙ le) ⟩
         frag (refl ×⟨ ⊎-∙ ⟩ refl)

do-send : ∀ {a α} → ∀[ ○ (Just (a ! α) ✴ Val a) ⇒ M (○ (Just (α .force))) ]
do-send = {!!}

-- a receive might be blocked by the lack of messages in the buffer,
-- in which case you will get an unmodified channel pointer back.
do-receive : ∀ {a α} → ∀[ ○ (Just (a ¿ α)) ⇒ M (○ ((Just (α .force) ✴ Val a) ∪ Just (a ¿ α))) ]
do-receive = {!!}

-- | Given a closure and a endpointer, fork of a computation
do-fork : ∀[ ○ (Closure (chan α) b ✴ Just α) ─✴ M Emp ]
do-fork = {!!}

step : ∀[ ○ (Thread a) ⇒ M (○ (Thread a ∪ Val a)) ]

step (frag (pure val)) =
  return (frag (inj₂ val))

step (frag (impure (send x ×⟨ σ₀ ⟩ κ))) =
  do-send (frag x) ⟪ neither (⊎-comm σ₀) ⟫= λ where
    (frag ch) (neither σ) → return (frag (inj₁ (κ ch σ)))

step (frag thread@(impure (receive ch ×⟨ σ₀ ⟩ κ))) =
  do-receive (frag ch) ⟪ neither (⊎-comm σ₀) ⟫= λ where
    -- no value in the buffer; reschedule
    (frag (inj₂ ch))   (neither σ) → return (frag (inj₁ (impure (receive ch ×⟨ ⊎-comm σ ⟩ κ))))
    -- received a value from the buffer
    (frag (inj₁ ch✴v)) (neither σ) → return (frag (inj₁ (κ ch✴v σ)))
    
step (frag (impure (close x ×⟨ σ ⟩ qx))) = {!!}

step (frag (impure (fork x  ×⟨ σ ⟩ qx))) = {!!}
