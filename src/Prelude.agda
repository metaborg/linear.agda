module Prelude where

open import Level public hiding (zero) renaming (suc to sucℓ)
open import Size public
open import Function public

open import Data.List using (List; _∷_; []; [_]) public
open import Data.Unit using (⊤; tt) public
open import Data.Nat using (ℕ; suc; zero; _+_) public
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _⊕_)public
open import Data.Product public hiding (map; zip)
open import Codata.Thunk public

open import Relation.Unary hiding (_∈_; Empty) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public

open import Relation.Ternary.Separation public
open import Relation.Ternary.Separation.Allstar public
