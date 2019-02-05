module Sessions.Syntax.Channels where

open import Level
open import Size
open import Function

open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.List as List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Codata.Thunk

open import Relation.Unary hiding (_∈_)
open import Relation.Unary.Separation
open import Relation.Nullary
open import Relation.Nullary.Decidable as DecM
open import Relation.Nullary.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Sessions.Syntax.Types

{- Channel types -}
module _ where
  open import Data.Maybe as Maybe renaming
    ( nothing to inactive
    ; just    to active
    ) public

  CType : Size → Set
  CType = Maybe ∘ SType

  -- mnemonics for different usages of lists of these things
  Channels  = List ∘ CType
  Endpoints = List ∘ CType

  -- mnemonics for the two sides of the channel type
  front back : ∀[ CType ⇒ CType ]
  front = id
  back  = Maybe.map _⁻¹

  -- take the ends of a channel
  ends : ∀[ CType ⇒ (CType ∩ CType) ]
  ends a = front a , back a

  -- take a list of channels into a list of all endpoints
  endpoints : ∀[ Channels ⇒ Endpoints ]
  endpoints [] = []
  endpoints (a ∷ ch) =
      front a
    ∷ back a
    ∷ endpoints ch
