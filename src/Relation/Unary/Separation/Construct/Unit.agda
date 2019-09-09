{- The trivial resource -}
module Relation.Unary.Separation.Construct.Unit where

open import Data.Unit
open import Data.Product

open import Relation.Unary
open import Relation.Unary.Separation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open RawSep
instance unit-raw-sep : RawSep ⊤
_⊎_≣_ unit-raw-sep = λ _ _ _ → ⊤

instance unit-has-sep : IsSep unit-raw-sep
unit-has-sep = record
  { ⊎-comm  = λ _   → tt
  ; ⊎-assoc = λ _ _ → tt , tt , tt
  }

instance unit-is-unital : IsUnitalSep _ _
unit-is-unital = record
  { isSep = unit-has-sep
  ; ⊎-idˡ = tt
  ; ⊎-id⁻ˡ = λ where tt → refl }

instance unit-sep : Separation _
unit-sep = record
  { isSep = unit-has-sep }
