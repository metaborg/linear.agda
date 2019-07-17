module Relation.Unary.Separation.Construct.Maybe where

open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

module _ (A : Set) ⦃ _ : RawSep A ⦄ where

  open RawSep ⦃...⦄
  
  MA = Maybe A

  data Split : MA → MA → MA → Set where
    on-right : ∀ {Φ} →                     Split nothing (just Φ) (just Φ)
    on-left  : ∀ {Φ} →                     Split (just Φ) nothing (just Φ)
    on-both  : ∀ {Φₗ Φᵣ Φ} → Φₗ ⊎ Φᵣ ≣ Φ → Split (just Φₗ) (just Φᵣ) (just Φ)
    neither  :                             Split nothing nothing nothing

  maybe-rawsep : RawSep (Maybe A)
  maybe-rawsep = record { _⊎_≣_ = Split }

  module _ where
    open IsSep

    postulate maybe-issep : IsSep _≡_ maybe-rawsep
    -- ⊎-functional maybe-issep = {!!}
    -- ⊎-cancellative maybe-issep = {!!}
    -- ⊎-comm maybe-issep = {!!}
    -- ⊎-assoc maybe-issep = {!!}

  maybe-separation : Separation _ _
  maybe-separation = record
    { set = setoid (Maybe A)
    ; raw = maybe-rawsep
    ; isSep = maybe-issep }
