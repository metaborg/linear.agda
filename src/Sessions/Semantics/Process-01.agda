module Sessions.Semantics.Process-01 where

open import Prelude hiding (_∷ʳ_; lift; Lift)
open import Data.Unit
open import Data.List.Relation.Ternary.Interleaving
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Data.List.Relation.Equality.Propositional

open import Relation.Unary
open import Relation.Unary.Separation.Construct.Auth
open import Relation.Unary.Separation.Construct.Product

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Expr-02

open Authoritative ⦃...⦄

-- A framed predicate
▤ = Pred (▣ SCtx) 0ℓ

data Lift (P : Pred (SCtx × SCtx) 0ℓ) : ▤ where
  lift : ∀ {Φ₁ Φ₂} → P (Φ₁ , Φ₂) → Lift P (Φ₁ ◐ Φ₂)

instance
  auth-raw : RawSep (▣ SCtx)
  auth-raw = auth-raw-sep

  auth-raw-unital : RawUnitalSep (▣ SCtx)
  auth-raw-unital = auth-unital

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

State : ▤
State = Lift Links ✴ ○ Pool

-- The monotone state monad
M : ▤ → ▤
M P = State ==✴ State ✴ P

return : ∀ {P} → ∀[ P ─✴ M P ]
return px st σ₁ σ₂ = {!!} -- -, -, σ₂ , st ×⟨ ⊎-comm σ₁ ⟩ px

join : ∀ {P} → ∀[ M (M P) ⇒ M P ]
join c st σ = ⤇-bind (apply ∘ ✴-swap) (apply (c ×⟨ σ ⟩ st))
  where open Update

mmap : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ M P ⇒ M Q ]
mmap f c st σ = ⤇-map ⟨ id ⟨✴⟩ f ⟩ (apply (c ×⟨ σ ⟩ st))
  where open Update

_>>=_ : ∀ {P Q} → ∀[ P ⇒ M Q ] → ∀[ M P ⇒ M Q ]
_>>=_ f = join ∘ mmap f

-- | Creating a new channel, returning two compatible endpoints and updated links
newChannel : ∀ α → ∀[ State ==✴ State ✴ ○ (Just α ✴ Just (α ⁻¹)) ]
newChannel α (lift ls ×⟨ σ₂ ⟩ th) σ₁ {Φⱼ = Φⱼ} {Φₖ = Φₖ₁ ◐ Φₖ₂ } σ =
  let
    new-state = lift (cons (newLink α ×⟨ consˡ (consˡ (right (≡⇒≋ refl))) , ⊎-identityˡ refl ⟩ ls)) ×⟨ {!!} ⟩ th
    pointers  = client (refl ×⟨ consˡ (consʳ []) ⟩ refl)
  in
   _ 
  , (α ∷ α ⁻¹ ∷ Φₖ₁) ◐ (α ∷ α ⁻¹ ∷ Φₖ₂)
  , {!!}
  , new-state ×⟨ authₗ (⊎-identityˡ refl) (≤-reflexive refl) ⟩ pointers
  -- _
  -- , (α ∷ α ⁻¹ ∷ proj₁ Φ , α ∷ α ⁻¹ ∷ proj₂ Φ)
  -- , ({!auth!} , {!!} ×⟨ {!!} ⟩ (client refl) ×⟨ client (consˡ (consʳ [])) ⟩ client refl)

do-send : ∀ {a α} → ∀[ ○ (Just (a ! α) ✴ Val a) ─✴ M (○ (Just (α .force))) ]
do-send = {!!}

-- a receive might be blocked by the lack of messages in the buffer,
-- in which case you will get an unmodified channel pointer back.
do-recv : ∀ {a α} → ∀[ ○ (Just (a ¿ α)) ─✴ M (○ ((Just (α .force) ✴ Val a) ∪ Just (a ¿ α))) ]
do-recv = {!!}

-- | Given a closure and a endpointer, fork of a computation
do-fork : ∀[ ○ (Closure (chan α) b ✴ Just α) ─✴ M Emp ]
do-fork = {!!}

step : ∀[ ○ (Thread a) ─✴ M (○ (Thread a ∪ Val a)) ]
step (client (pure val))     = return (client (inj₂ val))
step (client (impure cmd✴κ)) = {!!}
