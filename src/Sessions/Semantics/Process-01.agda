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

-- | The channel buffers and connections (predicates over `SCtx × SCtx`)
-- The left context is the 'authorative' part,
-- and the right context is the 'client' part

Buffer : SType ∞ → Pred (SCtx × SCtx) 0ℓ
Buffer = {!!}

empty : ∀ α → Buffer α ([ α ] , ε)
empty = {!!}

data Link : Pred (SCtx × SCtx) 0ℓ where
  link : ∀[ Buffer α ✴ Buffer (α ⁻¹) ⇒ Link ]

newLink : ∀ α → Link (α ∷ α ⁻¹ ∷ [] , ε)
newLink α = {!!} -- link (empty α ×⟨ {!!} ⟩ empty (α ⁻¹))

Links : Pred (SCtx × SCtx) 0ℓ
Links = Bigstar Link

-- | Threads are clients (predicates over `SCtx`)

Thread : Type ∞ → Pred SCtx 0ℓ
Thread a = F (Val a)

Pool : Pred SCtx 0ℓ
Pool = Bigstar (λ Φ → ∃ λ a → Thread a Φ)

-- | The server state (predicate over `▣ SCtx`)

State : fPred
State = Lift Links ✴ ○ Pool

-- The monotone state monad
M : fPred → fPred
M P = State ==✴ State ✴ P -- i.e. M P = State ─✴ (⤇ (State ✴ P))

return : ∀ {P} → ∀[ P ⇒ M P ]
return px st σ₁ σ₂ = -, -, σ₂ , st ×⟨ ⊎-comm σ₁ ⟩ px

join : ∀ {P} → ∀[ M (M P) ⇒ M P ]
join c st σ = ⤇-bind (apply ∘ ✴-swap) (apply (c ×⟨ σ ⟩ st))
  where open Update

-- external map
mmap : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ M P ⇒ M Q ]
mmap f c st σ = ⤇-map ⟨ id ⟨✴⟩ f ⟩ (apply (c ×⟨ σ ⟩ st))
  where open Update

-- internal map
imap : ∀ {P Q} → ∀[ M P ─✴ (P ⇒ Q) ─✴ M Q ]
imap f σ₁ c σ₂ st σ₃ = {!!}
  where open Update

-- this is the wrong bind; both the continuation and the monadic computation
-- use some amount of resource, but they are not disjoint
bind' : ∀ {P Q} → ∀[ P ⇒ M Q ] → ∀[ M P ⇒ M Q ]
bind' f = join ∘ mmap f

bind : ∀ {P Q} → ∀[ (P ─✴ M Q) ⇒ (M P ─✴ M Q) ]
bind = {!!}

-- | Creating a new channel, returning two compatible endpoints and updated links
newChannel : ∀ α → ε[ M (○ (Just α ✴ Just (α ⁻¹))) ]
newChannel α {Φₒ} (lift ls ×⟨ σ₂ ⟩ th) σ₁ {Φⱼ = Φⱼ} {Φₖ = Φₖ} σ = {!!}
  -- -- σ describe an arbitrary frame (Φⱼ) around what we own (x₁)
  -- --
  -- let
  --   new-state = lift (cons (newLink α ×⟨ consˡ (consˡ (right (≡⇒≋ refl))) , ⊎-identityˡ refl ⟩ ls)) ×⟨ {!!} ⟩ th
  --   pointers  = frag (refl ×⟨ consˡ (consʳ []) ⟩ refl)
  -- in
  -- -- (Φ₁ ◐ Φ₂) → ls
  -- -- Φᵣ        → th
  -- ----------------- +
  -- -- Φₚ = x
  -- ((α ∷ α ⁻¹ ∷ objective Φₒ) ◐ (α ∷ α ⁻¹ ∷ subjective Φₒ)) 
  -- , (α ∷ α ⁻¹ ∷ Φₖ₁) ◐ (α ∷ α ⁻¹ ∷ Φₖ₂)
  -- , {!!}
  -- , new-state ×⟨ {!!} ⟩ pointers -- authₗ (⊎-identityˡ refl) (≤-reflexive refl) ⟩ pointers
  -- -- _
  -- -- , (α ∷ α ⁻¹ ∷ proj₁ Φ , α ∷ α ⁻¹ ∷ proj₂ Φ)
  -- -- , ({!auth!} , {!!} ×⟨ {!!} ⟩ (frag refl) ×⟨ frag (consˡ (consʳ [])) ⟩ frag refl)

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
  bind
    (λ where (frag ch) (neither σ) → return (frag (inj₁ (κ ch σ))))
    (do-send (frag x))
    (neither (⊎-comm σ₀))
step (frag thread@(impure (receive ch ×⟨ σ₀ ⟩ κ))) =
  bind
    (λ where
      -- no value in the buffer; reschedule
      (frag (inj₂ ch))   (neither σ) → return (frag (inj₁ (impure (receive ch ×⟨ ⊎-comm σ ⟩ κ))))
      -- received a value from the buffer
      (frag (inj₁ ch✴v)) (neither σ) → return (frag (inj₁ (κ ch✴v σ))))
    (do-receive (frag ch))
    (neither (⊎-comm σ₀))
step (frag (impure (close x ×⟨ σ ⟩ qx))) = {!!}
step (frag (impure (fork x  ×⟨ σ ⟩ qx))) = {!!}
