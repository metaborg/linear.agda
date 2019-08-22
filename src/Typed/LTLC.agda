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

module LinearReader {v c t}
  {T : Set t}        -- types
  {C : Set c}        -- the separation carrier
  {V : T → Pred C v} -- values
  {{usep : RawUnitalSep C}} where

  CPred : (ℓ : Level) → Set (c ⊔ sucℓ ℓ)
  CPred ℓ = C → Set ℓ

  open RawUnitalSep usep using (sep)

  Reader : ∀ {p} → List T → List T → Pred C p → Pred C (c ⊔ t ⊔ v ⊔ p)
  Reader Γ₁ Γ₂ P = Allstar V Γ₁ ─✴ (Allstar V Γ₂ ✴ P)

  return : ∀ {p} {P : Pred C p} {{_ : IsSep sep}} →
           ∀[ P ⇒ Reader Γ Γ P ]
  return px e s = e ×⟨ ⊎-comm s ⟩ px

  return' : ∀ {p} {P : Pred C p} {{_ : IsUnitalSep usep}} →
            ε[ P ─✴ Reader Γ Γ P ]
  return' px σ₁ e σ₂ rewrite ⊎-identity⁻ˡ σ₁ = e ×⟨ ⊎-comm σ₂ ⟩ px

  bind : ∀ {p q} {P : Pred C p} {Q : Pred C q} {{_ : IsSep sep}} →
         ∀[ (P ─✴ Reader Γ₂ Γ₃ Q) ⇒ (Reader Γ₁ Γ₂ P ─✴ Reader Γ₁ Γ₃ Q) ]
  bind f mp σ₁ env σ₂ =
    let
      _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
      px✴env      = mp env σ₄
    in ✴-curry f (✴-swap px✴env) σ₃

  bind' = bind

  syntax bind  f p s = p ⟪ s ⟫= f
  syntax bind' f p = p ⟫= f

  frame : ∀ {p} {P : Pred C p} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
  frame sep c env s = {!!}
    -- let
    --   (E₁ ×⟨ E≺ ⟩ E₂) = LinearEnv.env-split sep env
    --   (Φ , eq₁ , eq₂) = ⊎-assoc E≺ (⊎-comm s)
    -- in bind
    --   (λ px s' → λ where (nil refl) s'' → E₂ ×⟨ subst (_ ⊎ _ ≣_) (⊎-identity⁻ʳ s'') s' ⟩ px)
    --   c eq₂ E₁ (⊎-comm eq₁)

  ask : {{_ : IsUnitalSep usep}} → ε[ Reader Γ ε (Allstar V Γ) ]
  ask env σ = nil ×⟨ σ ⟩ env

  asks : ∀ {p} {P : Pred C p} {{_ : IsUnitalSep usep}} → ∀[ (Allstar V Γ ─✴ P) ⇒ Reader Γ ε P ]
  asks f env σ =
    let px = f env σ
    in (nil ×⟨ ⊎-identityˡ ⟩ px)

  prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ∙ Γ₂) Emp ]
  prepend env₁ env₂ s = {!!} -- env-∙ (env₁ ×⟨ s ⟩ env₂) ×⟨ ⊎-identityʳ refl ⟩ refl

  append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ∙ Γ₁) Emp ]
  append env₁ env₂ s = {!!} -- env-∙ (env₂ ×⟨ ⊎-comm s ⟩ env₁) ×⟨ ⊎-identityʳ refl ⟩ refl

module _ {c}
  {C : Set c}        -- the separation carrier
  {{usep : RawUnitalSep C}} where

  CPred : (ℓ : Level) → Set (c ⊔ sucℓ ℓ)
  CPred ℓ = C → Set ℓ

  open RawUnitalSep usep using (sep)

  mutual
    Env : Ctx → CPred _
    Env = Allstar Val

    data Val : Ty → CPred c where
      num   : ℕ → ε[ Val nat ]
      clos  : ∀ {Γ} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

    open LinearReader {V = Val} {{ usep }}

    postulate lem : ∀ {x y y' z : C} → ε ⊎ y' ≣ y → x ⊎ y ≣ z → x ⊎ y' ≣ z

    {-# TERMINATING #-}
    eval : {{_ : IsUnitalSep usep }} → Exp a Γ → ε[ Reader Γ ε (Val a) ]

    eval (add (e₁ ×⟨ Γ≺ ⟩ e₂)) =
      frame Γ≺ (eval e₁) ⟪ ⊎-identityʳ ⟫= λ where
        (num n₁) → eval e₂ ⟫= λ where
          (num n₂) → return' (num (n₁ + n₂))  

    eval (num n) =
      return (num n)

    eval (lam e) =
      ask ⟪ ⊎-identityˡ ⟫= λ
        env → return' (clos e env)

    eval (app (f ×⟨ Γ≺ ⟩ e)) =
      frame (⊎-comm Γ≺) (eval e) ⟪ ⊎-identityʳ ⟫= λ where
        v σ₁ → eval f ⟪ ⊎-comm σ₁ ⟫= λ where
          (clos e env) σ₂ → append (singleton v) ⟪ ⊎-comm σ₂ ⟫= λ where
            refl σ₃ → append env ⟪ ⊎-comm σ₃ ⟫= λ where
              refl σ₄ → case (⊎-identity⁻ˡ σ₄) of λ where
                refl → eval e

    eval (var refl) = ask ⟪ ⊎-identityˡ ⟫= λ where
      (cons (px ×⟨ σ₁ ⟩ nil)) → case (⊎-identity⁻ʳ σ₁) of λ where
         refl → return' px
