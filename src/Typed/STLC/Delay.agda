open import Data.Nat
open import Data.Bool
open import Data.Product
open import Function
open import Data.List hiding (lookup)
open import Data.List.All
open import Data.List.Membership.Propositional
open import Data.Maybe.Categorical
open import Category.Monad
open import Agda.Primitive 
open import Size
open import Codata.Thunk
open import Codata.Delay
open import Codata.Delay.Categorical

module Typed.STLC.Delay where

data Ty : Set where
  numt boolt : Ty
  _⟶_ : Ty → Ty → Ty

data Expr : List Ty → Ty → Set where
  add : ∀ {Γ} →
    Expr Γ numt → Expr Γ numt →
    Expr Γ numt
  num : ∀ {Γ} →
    ℕ →
    Expr Γ numt
  true′ false′ : ∀ {Γ} →
    Expr Γ boolt
  if′_then_else : ∀ {Γ} →
    ∀ {t} → Expr Γ boolt → Expr Γ t → Expr Γ t →
    Expr Γ t
  ƛ_ : ∀ {Γ t₁ t₂} →
    Expr (t₁ ∷ Γ) t₂ →
    Expr Γ (t₁ ⟶ t₂)
  _∙_ : ∀ {Γ t₁ t₂} →
    Expr Γ (t₁ ⟶ t₂) → Expr Γ t₁ →
    Expr Γ t₂
  var : ∀ {Γ t} →
    t ∈ Γ →
    Expr Γ t
  

mutual
  data Val : Ty → Set where
    numv : ℕ → Val numt
    boolv : Bool → Val boolt
    ⟨ƛ_,_⟩ : ∀ {Γ t₁ t₂} → Expr (t₁ ∷ Γ) t₂ → Env Γ → Val (t₁ ⟶ t₂)

  Env : List Ty → Set
  Env Γ = All Val Γ

ReaderT : ∀ {a} {M : Set a → Set a} (R : Set a) → RawMonad M → RawMonad (λ A → R → M A)
ReaderT _ M = record { return = λ a _ → return a ;
                       _>>=_ = λ f k r → f r >>= λ x → k x r }
  where open RawMonad M

module _ {Γ : List Ty} {i} where
  open RawMonad {lzero} (ReaderT (Env Γ) (Sequential.monad {i})) public

M : List Ty → Size → Set → Set
M Γ i A = Env Γ → Delay A i

getEnv : ∀ {Γ i} → M Γ i (Env Γ)
getEnv E = now E

withEnv : ∀ {Γ Γ' i A} → Env Γ → M Γ i A → M Γ' i A
withEnv E m _ = m E

get : ∀ {Γ t i} → t ∈ Γ → M Γ i (Val t)
get x E = now (lookup E x)

mutual
  eval : ∀ {Γ t} → Expr Γ t → ∀ {i} → M Γ i (Val t)
  eval (add e₁ e₂) = do
    numv n₁ ← eval e₁
    numv n₂ ← eval e₁
    return (numv (n₁ + n₂))
  eval (num n) = do
    return (numv n)
  eval true′ = do
    return (boolv true)
  eval false′ = do
    return (boolv false)
  eval (if′ c then t else e) = do
    (boolv b) ← eval c
    if b then eval t else eval e
  eval (ƛ e) = do
    E ← getEnv
    return ⟨ƛ e , E ⟩
  eval (f ∙ a) = do
    ⟨ƛ e , E ⟩ ← eval f
    v ← eval a
    withEnv (v ∷ E) (▹eval e)
  eval (var x) = do
    get x

  ▹eval : ∀ {Γ i t} → Expr Γ t → M Γ i (Val t)
  ▹eval e E = later λ where .force → eval e E

