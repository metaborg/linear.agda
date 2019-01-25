module Sessions.Syntax.Channels where

open import Level
open import Size
open import Function

open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Codata.Thunk

open import Relation.Unary hiding (_∈_)
open import Relation.Nullary
open import Relation.Nullary.Decidable as DecM
open import Relation.Nullary.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Sessions.Syntax.Types

{- Channel Types -}
module _ where
  open import Data.Maybe renaming
    ( nothing to inactive
    ; just    to active
    ) public

  -- an (active?) endpoint with a type
  Endpoint = Maybe (SType ∞)
  Endpoints = List Endpoint

  open import Relation.Unary.Separation Endpoints id

  -- linear enpoint pointer
  data Endpointer : SType ∞ → Endpoints → Set where
    ptr : ∀ {α} → Endpointer α [ active α ]

  -- a channel is a pair of compatible endpoints
  Channel : SType ∞ → Endpoints → Set
  Channel α = Endpointer α ✴ Endpointer (α ⁻¹)
