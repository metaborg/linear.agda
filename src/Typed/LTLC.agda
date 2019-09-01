module Typed.LTLC where

open import Prelude
open import Function
open import Level
open import Category.Monad

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

module LinearReader {v c t}
  {T : Set t}        -- types
  {{m : MonoidalSep c}}
  {V : T → Pred (MonoidalSep.Carrier m) v} -- values
  where
  
  open MonoidalSep m

  CPred : (ℓ : Level) → Set (c ⊔ sucℓ ℓ)
  CPred ℓ = Carrier → Set ℓ

  Reader : ∀ {p} → List T → List T → CPred p → CPred (c ⊔ t ⊔ v ⊔ p)
  Reader Γ₁ Γ₂ P = Allstar V Γ₁ ─✴ (Allstar V Γ₂ ✴ P)

  return : ∀ {p} {P : CPred p} → ∀[ P ⇒ Reader Γ Γ P ]
  return px e s = e ×⟨ ⊎-comm s ⟩ px

  ireturn : ∀ {p} {P : CPred p}  → ε[ P ─✴ Reader Γ Γ P ]
  ireturn px σ₁ e σ₂ rewrite ⊎-id⁻ˡ σ₁ = e ×⟨ ⊎-comm σ₂ ⟩ px

  _<<=_ : ∀ {p q} {P : CPred p} {Q : CPred q} → 
          ∀[ P ⇒ Reader Γ₂ Γ₃ Q ] → ∀[ Reader Γ₁ Γ₂ P ⇒ Reader Γ₁ Γ₃ Q ]
  _<<=_ f mp env σ = let (env ×⟨ σ' ⟩ px) = mp env σ in f px env (⊎-comm σ')

  _>>=_ : ∀ {p q} {P : CPred p} {Q : CPred q} {Φ} → 
          Reader Γ₁ Γ₂ P Φ → ∀[ P ⇒ Reader Γ₂ Γ₃ Q ] → Reader Γ₁ Γ₃ Q Φ
  mp >>= f = f <<= mp

  ibind : ∀ {p q} {P : CPred p} {Q : CPred q} → 
          ∀[ (P ─✴ Reader Γ₂ Γ₃ Q) ⇒ (Reader Γ₁ Γ₂ P ─✴ Reader Γ₁ Γ₃ Q) ]
  ibind f mp σ₁ env σ₂ =
    let
      _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
      px✴env      = mp env σ₄
    in ✴-curry f (✴-swap px✴env) σ₃

  syntax ibind f p s = p ⟪ s ⟫= f

  ibind' : ∀ {p q} {P : SPred p} {Q : SPred q}  →
           ε[ (P ─✴ Reader Γ₂ Γ₃ Q) ─✴ Reader Γ₁ Γ₂ P ─✴ Reader Γ₁ Γ₃ Q ]
  ibind' f σ₀ mp σ₁ env σ₂ rewrite ⊎-id⁻ˡ σ₀ =
    let
      _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
      px✴env      = mp env σ₄
    in ✴-curry f (✴-swap px✴env) σ₃

  -- strength
  _^_ : ∀ {p q} {P : SPred p} {Q : SPred q} →
        ε[ Reader Γ₁ Γ₂ P ] → ∀[ Q ⇒ Reader Γ₁ Γ₂ (P ✴ Q)]
  (mp ^ qx) env σ with mp env ⊎-idˡ
  ... | env' ×⟨ σ' ⟩ px with ⊎-assoc σ' (⊎-comm σ)
  ... | _ , σ₂ , σ₃ = env' ×⟨ σ₂ ⟩ px  ×⟨ σ₃ ⟩ qx

  str : ∀ {p q} {P : SPred p} {Q : SPred q} →
        ∀[ Reader Γ₁ Γ₂ P ✴ Q ⇒ Reader Γ₁ Γ₂ (P ✴ Q)]
  str (mp ×⟨ σ ⟩ qx) env σ' with ⊎-assoc (⊎-comm σ) σ'
  ... | _ , σ₃ , σ₄ with mp env σ₄
  ... | env' ×⟨ σ'' ⟩ px with ⊎-assoc σ'' (⊎-comm σ₃) 
  ... | _ , σ₅ , σ₆ = env' ×⟨ σ₅ ⟩ px ×⟨ σ₆ ⟩ qx

  frame : ∀ {p} {P : CPred p} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ ε P ⇒ Reader Γ₂ Γ₃ P ]
  frame sep c env s = 
    let
      (E₁ ×⟨ E≺ ⟩ E₂) = env-split sep env
      (Φ , eq₁ , eq₂) = ⊎-assoc E≺ (⊎-comm s)
    in ibind
      (λ px s' → λ where nil s'' → E₂ ×⟨ subst (_ ⊎ _ ≣_) (⊎-id⁻ʳ s'') s' ⟩ px)
      c eq₂ E₁ (⊎-comm eq₁)

  ask : ε[ Reader Γ ε (Allstar V Γ) ]
  ask env σ = nil ×⟨ σ ⟩ env

  asks : ∀ {p} {P : CPred p} → ∀[ (Allstar V Γ ─✴ P) ⇒ Reader Γ ε P ]
  asks f env σ =
    let px = f env σ
    in (nil ×⟨ ⊎-idˡ ⟩ px)

  prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ∙ Γ₂) Emp ]
  prepend env₁ env₂ s = env-∙ (env₁ ×⟨ s ⟩ env₂) ×⟨ ⊎-idʳ ⟩ empty

  append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ∙ Γ₁) Emp ]
  append env₁ env₂ s = env-∙ (env₂ ×⟨ ⊎-comm s ⟩ env₁) ×⟨ ⊎-idʳ ⟩ empty

module _ {c} {{m : MonoidalSep c}} where
  open MonoidalSep m using (Carrier)

  CPred : (ℓ : Level) → Set (c ⊔ sucℓ ℓ)
  CPred ℓ = Carrier → Set ℓ

  mutual
    Env : Ctx → CPred _
    Env = Allstar Val

    data Val : Ty → CPred c where
      num   : ℕ → ε[ Val nat ]
      clos  : ∀ {Γ} → Exp b (a ∷ Γ) → ∀[ Env Γ ⇒ Val (a ⊸ b) ]

    open LinearReader {V = Val}

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
      clos e env ×⟨ σ ⟩ v ← str (eval f ×⟨ ⊎-idˡ ⟩ v)
      empty ×⟨ σ ⟩ env    ← str {Q = Allstar _ _} (append (singleton v) ×⟨ ⊎-comm σ ⟩ env)
      case (⊎-id⁻ˡ σ) of λ where
        refl → do
          empty ← append env
          eval e

    eval (var refl) = do
      cons (v ×⟨ σ ⟩ nil) ← ask
      case (⊎-id⁻ʳ σ) of λ where
        refl → return v

    -- {-# TERMINATING #-}
    -- eval : ε[ Empty (Exp a Γ) ─✴ Reader Γ ε (Val a) ]

    -- eval (emp (add (e₁ ×⟨ Γ≺ ⟩ e₂))) σ = {!!}
    --   bind′ {!!} {!!} (frame Γ≺ (eval (emp e₁) ⊎-idʳ) ⊎-idʳ) ⊎-idʳ
    --   frame Γ≺ (eval e₁) ⟪ ? ⟫= λ where
    --     (num n₁) → eval e₂ ⟫= λ where
    --       (num n₂) → return' (num (n₁ + n₂))  

    -- eval (emp (num n)) =
    --   ireturn (num n)

    -- eval (emp (lam e)) = 
    --   bind′ (λ env → ireturn (clos e env)) ⊎-idʳ (iask empty ⊎-idʳ)
    --   ask ⟪ ⊎-idˡ ⟫= λ
    --     env → return' (clos e env)

    -- eval (emp (app (f ×⟨ Γ≺ ⟩ e))) = {!!}
    --   frame (⊎-comm Γ≺) (eval e) ⟪ ⊎-idʳ ⟫= λ where
    --     v σ₁ → eval f ⟪ ⊎-comm σ₁ ⟫= λ where
    --       (clos e env) σ₂ → append (singleton v) ⟪ ⊎-comm σ₂ ⟫= λ where
    --         refl σ₃ → append env ⟪ ⊎-comm σ₃ ⟫= {!!} -- pure λ where
    --           -- refl → {!eval e!} -- case (⊎-id⁻ˡ σ₄) of λ where
    --             -- refl → eval e

    -- eval (emp (var refl)) = bind′ (λ where (cons (px ×⟨ σ₁ ⟩ nil)) → case (⊎-id⁻ʳ σ₁) of λ where refl → ireturn px) ⊎-idʳ (iask empty ⊎-idʳ) -- ask ⟪ ⊎-idˡ ⟫= λ where
    --   (cons (px ×⟨ σ₁ ⟩ nil)) → case (⊎-id⁻ʳ σ₁) of λ where
    --      refl → return' px
