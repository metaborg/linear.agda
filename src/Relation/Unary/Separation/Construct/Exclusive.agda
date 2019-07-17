module Relation.Unary.Separation.Construct.Exclusive where

open import Relation.Unary.Separation
open import Relation.Binary.PropositionalEquality
open import Data.Empty

module _ (A : Set) where
  record Ex : Set where
    constructor ex
    field
      part : A

  ex-rawsep : RawSep Ex
  ex-rawsep = record
    { _⊎_≣_ = λ _ _ _ → ⊥ }

  module _ where
    open IsSep

    ex-issep : IsSep _≡_ ex-rawsep
    ⊎-functional ex-issep ()
    ⊎-cancellative ex-issep ()
    ⊎-comm ex-issep ()
    ⊎-assoc ex-issep ()

  ex-separation : Separation _ _
  ex-separation = record
    { set = setoid Ex
    ; raw = ex-rawsep
    ; isSep = ex-issep }

  -- Ex A has no core, and therefor is not unital.
