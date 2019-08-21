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

instance unit-raw-unital : RawUnitalSep ⊤
unit-raw-unital = record { ε = tt ; sep = unit-raw-sep }

instance unit-has-sep : IsSep unit-raw-sep
unit-has-sep = record
  { ⊎-comm  = λ _   → tt
  ; ⊎-assoc = λ _ _ → tt , tt , tt
  }

instance unit-has-unit : RawUnitalSep ⊤
unit-has-unit = record
  { ε = tt
  ; sep = unit-raw-sep }

instance unit-is-unital : IsUnitalSep ⊤
unit-is-unital = record
  { unital = unit-has-unit
  ; isSep = unit-has-sep
  ; ⊎-identityˡ = λ x → tt
  ; ⊎-identity⁻ˡ = λ where tt → refl }

instance unit-sep : Separation _ _
unit-sep = record
  { set   = P.setoid ⊤
  ; isSep = unit-has-sep }
