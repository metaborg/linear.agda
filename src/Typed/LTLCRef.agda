module Typed.LTLCRef where

open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Function
open import Category.Monad

open import Relation.Unary.Separation 
open import Relation.Unary.Separation.Env
open import Relation.Unary.Separation.Construct.List as L

open import Prelude hiding (Lift; lookup)

data Ty : Set where
  nat  : Ty
  unit : Ty
  ref  : Ty → Ty
  _⊸_  : (a b : Ty) → Ty

Ctx  = List Ty
CtxT = List Ty → List Ty

open import Relation.Unary.Separation.Construct.Auth Ctx
open import Relation.Unary.Separation.Construct.Product

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
  num   : ℕ → ε[ Exp nat ]
  lam   : ∀[ (a ◂ id ⊢ Exp b) ⇒ Exp (a ⊸ b) ]
  app   : ∀[ Exp (a ⊸ b) ✴ Exp a ⇒ Exp b ]
  var   : ∀[ Just a ⇒ Exp a ]
  ref   : ∀[ Exp a ⇒ Exp (ref a) ]
  deref : ∀[ Exp (ref a) ⇒ Exp a ]
  asgn  : ∀[ Exp (ref a) ✴ Exp (a ⊸ b) ⇒ Exp (ref b) ]

-- store types
ST = List Ty

-- values
data Val : Ty → Pred ST 0ℓ where
  unit  :     ε[ Val unit ]
  num   : ℕ → ε[ Val nat  ]
  clos  : Exp b (a ∷ Γ) → ∀[ Allstar Val Γ ⇒ Val (a ⊸ b) ]
  ref   : ∀[ Just a ⇒ Val (ref a) ]

data Cell : Pred (ST × ST) 0ℓ where
  cell : ∀ {Σ} → Val a Σ → Cell ([ a ] , Σ)

-- typed stores
St : Pred Auth 0ℓ
St = Lift (Bigstar Cell)

AP : (ℓ : Level) → Set (sucℓ ℓ)
AP ℓ = Pred Auth ℓ

_⇒[_]_ : ∀ {a b p q} {A : Set a} {B : Set b} →
         (P : A → Set p) → (A → B) → (Q : B → Set q) → A → Set _
P ⇒[ f ] Q = λ a → P a → Q (f a)

M : ∀ {p} → Ctx → Ctx → Pred Ctx p → Pred Auth p
M Γ₁ Γ₂ P =
  (○ (Allstar Val Γ₁)) ─✴
  St ==✴
  (○ P) ✴ (○ (Allstar Val Γ₂)) ✴ St

return : ∀ {p} {Γ} {P : Pred Ctx p} → ∀[ P ⇒[ ◌ ] M Γ Γ P ]
return px env σ₂ st σ₃ =
  let _ , σ₄ , σ₅ = ⊎-assoc σ₂ σ₃ in
  ⤇-return ({!!} ×⟨ σ₄ ⟩ env ×⟨ σ₅ ⟩ st) ⊎-idˡ

_<<=_ : ∀ {p q} {P : Pred Ctx p} {Q : Pred Ctx q} → 
        ∀[ P ⇒[ ◌ ] M Γ₂ Γ₃ Q ] → ∀[ M Γ₁ Γ₂ P ⇒ M Γ₁ Γ₃ Q ]
_<<=_ f mp = {!!}

_>>=_ : ∀ {p q Φ} {P : Pred Ctx p} {Q : Pred Ctx q} → M Γ₁ Γ₂ P Φ → ∀[ P ⇒[ ◌ ] M Γ₂ Γ₃ Q ] → M Γ₁ Γ₃ Q Φ
mp >>= f = f <<= mp

str : ∀ {p q} {P : Pred Ctx p} {Q : Pred Ctx q} → ∀[ M Γ₁ Γ₂ P ✴ (○ Q) ⇒ M Γ₁ Γ₂ (P ✴ Q)]
str = {!!}

ask : ε[ M Γ ε (Allstar Val Γ) ]
ask env σ = {!!} -- nil ×⟨ σ ⟩ env

frame : ∀ {p} {P : Pred Ctx p} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ M Γ₁ ε P ⇒ M Γ₂ Γ₃ P ]
frame = {!!}

append : ∀[ Allstar Val Γ₁ ⇒[ ◌ ] M Γ₂ (Γ₂ ∙ Γ₁) Emp ]
append = {!!}

store : ∀[ Val a ⇒[ ◌ ] M Γ Γ (Just a) ]
store = {!!}

-- lookup : ε[ St ─✴ ○ (Just a) ==✴ ○ (Val a) ✴ St ]
-- lookup (lift st σ₀) (on-right σ₁) (frag refl) (on-left σ₂) with ⊎-id⁻ˡ σ₁

-- lookup (lift (cons (c ×⟨ σ ⟩ st)) (consˡ σ₀)) _ (frag refl) (on-left σ₂) | refl = {!st!}
-- lookup (lift st (consʳ σ₀)) _ (frag refl) (on-left σ₂) | refl = {!σ!}

-- -- store traversal
-- -- st-lookup (lift (cons (v ×⟨ σ ⟩ st)) (consˡ σ₀)) (on-right _) (frag refl) (on-left (consˡ σ₂)) | refl = λ φ → {!!} , {!!} , {!!} , frag {!v!} ×⟨ {!!} ⟩ {!!}
-- -- st-lookup (lift st (consʳ σ₀)) (on-right _) (frag refl) (on-left (consˡ σ₂)) | refl = {!!}

do-deref : ∀ {Γ} → ∀[ Just a ⇒[ ◌ ] M Γ Γ (Val a) ]
do-deref ptr σ₀ env σ₁ st σ₂ = {!!}

do-update : ∀[ Val a ⇒[ ◌ ] M Γ₁ Γ₂ (Val b) ] → ∀[ Just a ⇒[ ◌ ] M Γ₁ Γ₂ (Just b) ]
do-update = {!!}

--   -- let
--   --   _ , ρ₀ , ρ₁ = ⊎-assoc (⊎-comm σ₀) σ₁
--   --   _ , ρ₂ , ρ₃ = ⊎-assoc ρ₀ σ₂
--   -- in
--   -- ⤇-bind
--   --   (λ where (v ×⟨ σ₃ ⟩ st) σ₄ → ⤇-return (v ×⟨ {!!} ⟩ env ×⟨ {!!} ⟩ st) ⊎-idˡ)
--   --   ⊎-idˡ
--   --   (st-lookup st ⊎-idˡ ptr {!!}) {!!}

{-# TERMINATING #-}
mutual
  eval⊸ : ∀ {Γ} → Exp (a ⊸ b) Γ → ∀[ Val a ⇒[ ◌ ] M Γ ε (Val b) ]
  eval⊸ e v = do
    clos e env ×⟨ σ₂ ⟩ v ← str {Q = Val _} (eval e ×⟨ ⊎-idˡ ⟩ (frag v))
    empty                ← append (cons (v ×⟨ ⊎-comm σ₂ ⟩ env))
    eval e

  eval : ∀ {Γ} → Exp a Γ → ε[ M Γ ε (Val a) ]

  eval (num n) = do
    return (num n)

  eval (var refl) = do
    (v :⟨ σ ⟩: nil) ← ask
    case ⊎-id⁻ʳ σ of λ where
      refl → return v

  eval (lam e) = do
    env ← ask
    return (clos e env)

  eval (app (f ×⟨ Γ≺ ⟩ e)) = do
    v ← frame (⊎-comm Γ≺) (eval e)
    eval⊸ f v

  eval (ref e) = do
    v ← eval e
    r ← store v
    return (ref r)

  eval (deref e) = do
    ref r ← eval e
    do-deref r

  eval (asgn (e₁ ×⟨ σ ⟩ e₂)) = do
    ref ra ← frame σ (eval e₁)
    rb     ← do-update (eval⊸ e₂) ra
    return (ref rb)
