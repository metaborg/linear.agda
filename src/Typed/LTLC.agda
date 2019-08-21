module Typed.LTLC where

open import Prelude
open import Relation.Unary hiding (_∈_)
open import Function
open import Level
open import Category.Monad

open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Unit

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

rPred = ⊤ → Set

module LinearReader {p v c t}
  {T : Set t}        -- types
  {C : Set c}        -- the separation carrier
  {V : T → Pred C v} -- values
  {{usep : RawUnitalSep C}} where

  open RawUnitalSep usep using (sep)

  Reader : List T → List T → Pred C p → Pred C (c ⊔ t ⊔ v ⊔ p)
  Reader Γ₁ Γ₂ P = Allstar V Γ₁ ─✴ (Allstar V Γ₂ ✴ P)

  return : ∀ {P} {{_ : IsSep sep}} →
           ∀[ P ⇒ Reader Γ Γ P ]
  return px e s = e ×⟨ ⊎-comm s ⟩ px

  bind : ∀ {P Q} {{_ : IsSep sep}} →
         ∀[ (P ─✴ Reader Γ₂ Γ₃ Q) ⇒ (Reader Γ₁ Γ₂ P ─✴ Reader Γ₁ Γ₃ Q) ]
  bind f mp σ₁ env σ₂ =
    let
      _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
      px✴env      = mp env σ₄
    in ✴-curry f (✴-swap px✴env) σ₃

  syntax bind f p s = p ⟪ s ⟫= f

  frame : ∀ {P} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
  frame sep c env s = {!!}
    -- let
    --   (E₁ ×⟨ E≺ ⟩ E₂) = LinearEnv.env-split sep env
    --   (Φ , eq₁ , eq₂) = ⊎-assoc E≺ (⊎-comm s)
    -- in bind
    --   (λ px s' → λ where (nil refl) s'' → E₂ ×⟨ subst (_ ⊎ _ ≣_) (⊎-identity⁻ʳ s'') s' ⟩ px)
    --   c eq₂ E₁ (⊎-comm eq₁)

mutual
  Env : Ctx → rPred
  Env = Allstar Val

  data Val : Ty → rPred where
    num   : ℕ → ε[ Val nat ]
    clos  : ∀ {Γ} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

  open LinearReader renaming (Reader to M)

  -- eval : ∀ {Γ} → Exp a Γ → ∀[ M Γ ε (Val a) ]
  -- eval (add (e₁ ×⟨ Γ≺ ⟩ e₂)) =
  --   frame Γ≺ (eval e₁) ⟪ ⊎-identityˡ refl ⟫= λ where
  --     (num n) σ₁ → eval e₂ ⟪ σ₁ ⟫= λ where
  --       (num m) σ₂ → return (num (n + m))
  -- eval (num n) = return (num n)
  -- eval (lam e) = {!!}
  -- eval (app f✴e) = {!!}
  -- eval (var x) = {!!}

-- module Arrowic where
  -- first : {P Q R : Pred Ctx 0ℓ} →
  --         ∀[ P ⇒ Q ] →
  --         ∀[ (P ✴ R) ⇒
  --            (Q ✴ R) ]
  -- first = {!!}

  -- _>>>_ : ∀ {P Q R : Pred Ctx 0ℓ} →
  --         ∀[ P ⇒ Q ] →
  --         ∀[ Q ⇒ R ] →
  --         ∀[ P ⇒ R ]
  -- x >>> y = {!!}

  -- mapM′ : ∀ {A B} →
  --         (A → B) →
  --         ∀[ M A ⇒ M B ]
  -- mapM′ = {!!}
