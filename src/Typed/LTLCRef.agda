module Typed.LTLCRef where

open import Data.List.All
open import Data.List.Relation.Ternary.Interleaving.Propositional
open import Relation.Unary hiding (_∈_)
open import Function
open import Category.Monad

open import Relation.Unary.Separation 
open import Relation.Unary.Separation.Construct.List as L

open import Prelude hiding (Lift)

open L.LinearEnv

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

data Exp : Ty → Ctx → Set where
  num   : ∀[ Emp ⇒ Exp nat ]
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
  clos  : ∀ {Γ} → Exp b Γ → ∀[ Env Val Γ ⇒ Val (a ⊸ b) ]
  ref   : ∀[ Just a ⇒ Val (ref a) ]

data Cell : Pred (ST × ST) 0ℓ where
  cell : ∀ {Σ} → Val a Σ → Cell ([ a ] , Σ)

-- typed stores
St : Pred Auth 0ℓ
St = Lift (Bigstar Cell)

M : ∀ {p} → Ctx → Ctx → Pred Auth p → Pred Auth p
M Γ₁ Γ₂ P =
  (○ (Env Val Γ₁)) ─✴
  St ==✴
  P ✴ (○ (Env Val Γ₂)) ✴ St

return : ∀ {p} {Γ} {P : Pred Auth p} → ε[ P ─✴ M Γ Γ P ]
return px σ₁ env σ₂ st σ₃ rewrite ⊎-identity⁻ˡ σ₁ =
  let _ , σ₄ , σ₅ = ⊎-assoc σ₂ σ₃ in
  ⤇-return (px ×⟨ σ₄ ⟩ env ×⟨ σ₅ ⟩ st) ⊎-identityˡ

st-lookup : ε[ St ─✴ ○ (Just a) ==✴ ○ (Val a) ✴ St ]
st-lookup (lift st σ₀) (on-right σ₁) (frag refl) (on-left σ₂) with ⊎-identity⁻ˡ σ₁

st-lookup (lift (cons (c ×⟨ σ ⟩ st)) (consˡ σ₀)) _ (frag refl) (on-left σ₂) | refl = {!st!}
st-lookup (lift st (consʳ σ₀)) _ (frag refl) (on-left σ₂) | refl = {!σ!}

-- store traversal
-- st-lookup (lift (cons (v ×⟨ σ ⟩ st)) (consˡ σ₀)) (on-right _) (frag refl) (on-left (consˡ σ₂)) | refl = λ φ → {!!} , {!!} , {!!} , frag {!v!} ×⟨ {!!} ⟩ {!!}
-- st-lookup (lift st (consʳ σ₀)) (on-right _) (frag refl) (on-left (consˡ σ₂)) | refl = {!!}

do-deref : ∀ {Γ} → ∀[ ○ (Just a) ─✴ M Γ Γ (○ (Val a)) ]
do-deref ptr σ₀ env σ₁ st σ₂ = {!!}
  -- let
  --   _ , ρ₀ , ρ₁ = ⊎-assoc (⊎-comm σ₀) σ₁
  --   _ , ρ₂ , ρ₃ = ⊎-assoc ρ₀ σ₂
  -- in
  -- ⤇-bind
  --   (λ where (v ×⟨ σ₃ ⟩ st) σ₄ → ⤇-return (v ×⟨ {!!} ⟩ env ×⟨ {!!} ⟩ st) ⊎-identityˡ)
  --   ⊎-identityˡ
  --   (st-lookup st ⊎-identityˡ ptr {!!}) {!!}

eval : ∀ {Γ} → Exp a Γ →  ∀[ M Γ ε (○ (Val a)) ]
eval (num x) = {!!}
eval (lam e) = {!!}
eval (app f✴e) = {!!}
eval (var x) = {!!}
eval (ref e) = {!!}
eval (deref e) = {!!}
eval (asgn e₁✴e₂) = {!!}

module Ex where
  content' : Bigstar Cell (unit ∷ [ ref unit ] , [ unit ])
  content' =   cons (cell unit         ×⟨ consˡ (consʳ []) , ⊎-identityˡ ⟩
               cons (cell (ref refl)   ×⟨ ⊎-identityʳ      , ⊎-identityʳ  ⟩ 
               emp))
