module Typed.LTLC where

open import Prelude
open import Function
open import Level
open import Category.Monad

open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Unit
open import Relation.Unary.Separation.Env

data Ty : Set where
  nat  : Ty
  _⊸_ : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

infixr 20 _◂_
_◂_ : Ty → CtxT → CtxT
(x ◂ f) Γ = x ∷ f Γ

Just : Ty → Pred Ctx _
Just t = Exactly (t ∷ ε)

variable a b : Ty
variable ℓv  : Level
variable τ   : Set ℓv
variable Γ Γ₁ Γ₂ Γ₃ : List τ

data Exp : Ty → Ctx → Set where
  add : ∀[ Exp nat ✴ Exp nat ⇒ Exp nat ]
  num : ℕ → ε[ Exp nat ]
  lam : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  app : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var : ∀[ Just a ⇒ Exp a ]

module _ {a b} {A : Set a} {B : Set b} where
  _⇒[_]_ : ∀ {p q} (P : Pred A p) → (A → B) → (Q : Pred B q) → A → Set _
  P ⇒[ f ] Q = λ a → P a → Q (f a)

module _ {ℓ} {A : Set ℓ} {{sep : RawSep A}} {u} {{as : IsUnitalSep sep u}} where
  _─✴[_]_ : ∀ {b p q} {B : Set b} (P : A → Set p) → (A → B) → (Q : B → Set q) → A → Set _
  P ─✴[ j ] Q = P ─✴ (Q ∘ j)

module _
  {a b i} {A : Set a} {B : Set b} {I : Set i}
  {{sep : RawSep A}} {u} {{as : IsUnitalSep sep u}}
  {{ sep : RawSep B }}
  {j : A → B}
  {{ bs : IsUnitalSep sep (j ε) }} where

  {- strong, relative, indexed monads on predicates over SAs -}
  record SA-SRMonad {ℓ} (M : (i j : I) → PT A B ℓ ℓ) : Set (a ⊔ b ⊔ sucℓ ℓ ⊔ i) where
    field
      return : ∀ {P i₁}         → ∀[ P ⇒[ j ] M i₁ i₁ P ]
      bind   : ∀ {P i₁ i₂ i₃ Q} → ∀[ (P ─✴[ j ] M i₂ i₃ Q) ⇒[ j ] (M i₁ i₂ P ─✴ M i₁ i₃ Q) ]

    _=<<_ : ∀ {P Q i₁ i₂ i₃} → ∀[ P ⇒[ j ] M i₂ i₃ Q ] → ∀[ M i₁ i₂ P ⇒ M i₁ i₃ Q ]
    f =<< mp = bind (λ px σ → case ⊎-id⁻ˡ σ of λ where refl → f px) mp ⊎-idˡ  

    _>>=_ : ∀ {Φ} {P Q i₁ i₂ i₃} → M i₁ i₂ P Φ → ∀[ P ⇒[ j ] M i₂ i₃ Q ] → M i₁ i₃ Q Φ
    mp >>= f = f =<< mp

  open SA-SRMonad ⦃...⦄ public

module _
  {a b i} {A : Set a} {B : Set b} {I : Set i}
  {{sep : RawSep A}} {u} {{as : IsUnitalSep sep u}}
  {{ sep : RawSep B }}
  {j : A → B}
  {{ bs : IsUnitalSep sep (j ε) }} where

  data J (P : Pred A a) : Pred B (sucℓ a) where
    inj : P Φ → J P (j Φ)

  -- having the internal bind is enough to get strength
  str : ∀ {P i₁ i₂} {M : (i j : I) → PT A B a a} {{ _ : SA-SRMonad M }} (Q : Pred A a) →
        (M i₁ i₂ P ✴ J Q) Φ → M i₁ i₂ (P ✴ Q) Φ
  str _ (mp ×⟨ σ ⟩ inj qx) = bind (λ px σ' → return (px ×⟨ ⊎-comm σ' ⟩ qx)) mp (⊎-comm σ)

  syntax str Q mp qx = mp &[ Q ] qx

module LinearReader {ℓ}
  {T : Set ℓ}        -- types
  {{m : MonoidalSep ℓ}}
  (V : T → Pred (MonoidalSep.Carrier m) ℓ) -- values
  where
  
  open MonoidalSep m using (Carrier)

  variable
    P Q R : Pred Carrier ℓ

  record Reader (Γ₁ Γ₂ : List T) (P : Pred Carrier ℓ) (Φ : Carrier) : Set ℓ where
    constructor reader
    field
      runReader : (Allstar V Γ₁ ─✴ (Allstar V Γ₂ ✴ P)) Φ

  open Reader

  instance
    reader-monad : SA-SRMonad Reader
    SA-SRMonad.return reader-monad px = reader λ e s → e ×⟨ ⊎-comm s ⟩ px
    SA-SRMonad.bind   reader-monad f mp σ₁ = reader λ env σ₂ →
      let
        _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
        env ×⟨ σ₅ ⟩ px = runReader mp env σ₄
        _ , σ₆ , σ₇ = ⊎-unassoc σ₃ (⊎-comm σ₅) 
      in runReader (f px σ₆) env σ₇

  frame : Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
  frame sep c = reader λ env σ →
    let
      E₁ ×⟨ σ₁ ⟩ E₂ = env-split sep env
      Φ , σ₂ , σ₃   = ⊎-unassoc σ σ₁
    in case runReader c E₁ σ₂ of λ where
      (nil ×⟨ σ₄ ⟩ px) → case ⊎-id⁻ˡ σ₄ of λ where
        refl → E₂ ×⟨ ⊎-comm σ₃ ⟩ px

  ask : ε[ Reader Γ ε (Allstar V Γ) ]
  ask = reader λ env σ → nil ×⟨ σ ⟩ env

  prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ∙ Γ₂) Emp ]
  prepend env₁ = reader λ env₂ s → env-∙ (env₁ ×⟨ s ⟩ env₂) ×⟨ ⊎-idʳ ⟩ empty

  append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ∙ Γ₁) Emp ]
  append env₁ = reader λ env₂ s → env-∙ (env₂ ×⟨ ⊎-comm s ⟩ env₁) ×⟨ ⊎-idʳ ⟩ empty

module _ {{m : MonoidalSep 0ℓ}} where
  open MonoidalSep m using (Carrier)

  CPred : Set₁
  CPred = Carrier → Set

  mutual
    Env : Ctx → CPred
    Env = Allstar Val

    data Val : Ty → CPred where
      num   : ℕ → ε[ Val nat ]
      clos  : Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

  open LinearReader Val

  {-# TERMINATING #-}
  eval : Exp a Γ → ε[ Reader Γ ε (Val a) ]

  eval (num n) = do
    return (num n)

  eval (add (e₁ ×⟨ Γ≺ ⟩ e₂)) = do
    (num n₁) ← frame Γ≺ (eval e₁)
    (num n₂) ← eval e₂
    return (num (n₁ + n₂))

  eval (lam e) = do
    env ← ask
    return (clos e env)

  eval (app (f ×⟨ Γ≺ ⟩ e)) = do
    v                   ← frame (⊎-comm Γ≺) (eval e)
    clos e env ×⟨ σ ⟩ v ← str _ (eval f ×⟨ ⊎-idˡ ⟩ inj v)
    empty ×⟨ σ ⟩ env    ← str (Allstar _ _) (append (singleton v) ×⟨ ⊎-comm σ ⟩ inj env)
    case (⊎-id⁻ˡ σ) of λ where
      refl → do
        empty ← append env
        eval e

  eval (var refl) = do
    cons (v ×⟨ σ ⟩ nil) ← ask
    case (⊎-id⁻ʳ σ) of λ where
      refl → return v
