{-# OPTIONS --sized-types #-}
module Sessions.Syntax.Runtime where

open import Size
open import Level
open import Data.Product
open import Data.Sum
open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality as P
open import Data.List
open import Codata.Thunk

open import Sessions.Syntax.Types as T
open import Sessions.Syntax.Expr

open UnitalSep ⦃...⦄

-- `q : Queue (a ⊗ α)` denotes that a message of type a is waiting in q.
-- When this message is read, the queue remainder is typed α.
data Queue (i : Size) : SType ∞ → Pred SCtx 0ℓ where
  empty : ∀[ Emp ⇒ Queue i end ] 
  cons  : ∀ {α} →
          ∀[   Val a
             ✴ (λ Δ → Thunk[ j < i ] (Queue j (α .force) Δ))
             ⇒ Queue i (a ⊗ α) ]

-- -- A `Buffer α β` has two (typed) ends and can have messages waiting on either end.
-- -- 
-- data Buffer : SType ∞ → SType ∞ → SCtx → Set where
--   atₗ : ∀ {α' b β} → ∞ T.⊢ α' ≈ₛ (α ⁻¹) → ∀[ Queue ∞ α' (b ⅋ β) ⇒ Buffer (b ⅋ β) α ]
--   atᵣ : ∀ {α' b β} → ∞ T.⊢ α' ≈ₛ (α ⁻¹) → ∀[ Queue ∞ α' (b ⅋ β) ⇒ Buffer α (b ⅋ β) ]

-- -- queue-lem : ∀ {b β} → Queue i α (b ⅋ β) → ¬ α ≈
-- data Thread : Pred SCtx 0ℓ where
--   ⟨_,_⟩ : ∀ {a Δ} → Exp a Δ → ∀[ Env Δ ⇒ Thread ]

-- Buffers : SCtx → Pred SCtx 0ℓ
-- Buffers ends Δ = {!!}

-- Threads : Pred SCtx 0ℓ
-- Threads = Allstar Thread

-- record Runtime : Set where
--   field
--     {ends} : List (SType ∞)
--     pool   : (Buffers ends ✴ Threads) ends

-- {- Manipulating the buffers -}
-- module _ where

--   -- _[_]≔_ : ∀ {a} → SCtx → EndPtr a → SType → SCtx

--   -- This write type requires a dependency between the hole
--   -- and the first projection from the input.
--   -- write : ∀ {α eps Δ} → (i : (Just (a ⊗ α) ✴ Val a ✴ Buffers eps) Δ) → Buffers {!!} Δ
--   -- write p = {!!}

--   writeₗ : ∀ {a α β} → ∀[ Val a ✴ Buffer (a ⊗ α) β ⇒ Buffer (α .force) β ]
--   writeₗ (v IsSep.×⟨ σ₁ ⟩ atᵣ (-⅋ x) q) = atᵣ (x .force) (cons (v IsSep.×⟨ σ₁ ⟩ (λ where .force → q)))

--   readₗ : ∀ {a α β} → ∀[ Buffer (a ⅋ α) β ⇒ ((Val a ✴ Buffer (α .force) β) ∪ (Buffer (a ⅋ α) β)) ]
--   readₗ (atₗ z (empty x)) = inj₂ (atₗ z (empty x))
--   readₗ (atₗ z (cons (a IsSep.×⟨ sep ⟩ q))) = inj₁ ({!a!} IsSep.×⟨ {!!} ⟩ {!!})
--   readₗ (atᵣ z x₁) = {!x₁!}

-- module QueueExamples where
--   private
--     -- empty queue
--     ex₁ : Queue _ α α ε
--     ex₁ = empty P.refl

--     unit►unit► : Thunk SType ⊆ SType
--     unit►unit► α = unit ⅋ (λ where .force → unit ⅋ α)

--     -- 1 element queue
--     -- unit at ( unit ⅋ unit ⅋ α ) : Queue (unit ⅋ α) (unit ⅋ unit ⅋ α)
--     ex₂ : ∀ {α} → Queue ∞ (unit ⅋ α) (unit►unit► α) ε
--     ex₂ =
--         cons (tt P.refl IsSep.×⟨ ⊎-identityˡ P.refl ⟩ λ where
--           .force → ex₁)

--     -- 2 element queue
--     -- unit ∷ unit at ( unit ⅋ unit ⅋ α ) : Queue (unit ⅋ α) (unit ⅋ unit ⅋ α)
--     ex₃ : ∀ {α} → Queue ∞ (α .force) (unit►unit► α) ε
--     ex₃ {β} =
--         cons (tt P.refl IsSep.×⟨ ⊎-identityˡ P.refl ⟩ λ where
--           .force → ex₂ {β})

--   private
--     -- ε at α   ↭   unit ∷ unit at (unit ⅋ unit ⅋ α)
--     buf₁ : ∀ {α} → Buffer ((α .force) ⁻¹) (unit►unit► α) ε
--     buf₁ {α} = atᵣ {!!} {!ex₃!} -- (ex₃ {α} , P.refl)
