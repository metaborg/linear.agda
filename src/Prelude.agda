module Prelude where

open import Level public hiding (zero) renaming (suc to sucℓ)
open import Size public
open import Function public

open import Data.Nat using (ℕ; suc; zero; _+_) public
open import Data.Product public hiding (map; zip)
open import Data.List public hiding (map; zip)
open import Codata.Thunk public

open import Relation.Unary hiding (_∈_) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public

open import Relation.Unary.Separation public

open MonoidalSep ⦃...⦄ hiding (isEquivalence; isPreorder; preorder; refl; sym; trans) public
open Unital      ⦃...⦄ public

