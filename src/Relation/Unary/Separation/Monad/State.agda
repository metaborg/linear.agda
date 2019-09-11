open import Relation.Unary
open import Data.List

module Relation.Unary.Separation.Monad.State {ℓ} {T : Set ℓ} {V : T → Pred (List T) ℓ} where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Unary.Separation
open import Relation.Unary.Separation.Construct.List
open import Relation.Unary.Separation.Construct.Product
open import Relation.Unary.Separation.Construct.Market
open import Relation.Unary.Separation.Monad
open import Relation.Unary.Separation.Monad.Update

open import Data.Unit
open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional as I

private
  ST = List T

module _ where

  data Cell : Pred (ST × ST) ℓ where
    cell : ∀ {a Σ} → V a Σ → Cell ([ a ] , Σ)

  -- typed stores in auth
  Cells : Pred (ST × ST) ℓ
  Cells = Bigstar Cell

  St : Pred (Market ST) ℓ
  St = ● Cells

  M : Pred (List T) ℓ → Pred (Market (List T)) ℓ
  M P = St ==✴ (○ P) ✴ St

  -- without the strong monadic structure on update, the bind is terrible
  -- private
  --   thebind : ∀ {P Q : Pred ST ℓ} → ∀[ (P ─✴[ ◌ ] M Q) ⇒[ ◌ ] (M P ─✴ St ─✴ ⤇' ((○ Q) ✴ St)) ]
  --   thebind f m σ₁ st σ₂ fr                  with ⊎-assoc σ₁ σ₂
  --   ... | m+st , σ₃ , σ₄                     with ⊎-assoc (⊎-comm σ₃) fr
  --   ... | _ , σ₅ , σ₆                        with update (m st σ₄) σ₅
  --   ... | _ , _ , σ₅' , frag px ×⟨ σ₆' ⟩ st' with ⊎-assoc (⊎-comm σ₆') σ₅'
  --   ... | _ , σ₇ , σ₈                        with ⊎-assoc (⊎-comm σ₆) (⊎-comm σ₈)
  --   ... | _ , τ₁ , neither τ₂                with ⊎-unassoc σ₇ (⊎-comm τ₁)
  --   ... | _ , τ₃ , τ₄                        with f px τ₂ st' (⊎-comm τ₃)
  --   ... | local update = update τ₄

  instance
    M-monad : Monad {I = ⊤} (λ _ _ → M)
    Monad.return M-monad px st σ₂ = return (frag px ×⟨ σ₂ ⟩ st )
    Monad.bind M-monad {Q = Q} f m σ₁ st σ₂ = do
      let _ , σ₃ , σ₄                      = ⊎-assoc σ₁ σ₂
      -- we run m, and carry f across
      (frag px ×⟨ σ₅ ⟩ st') ×⟨ σ₆ ⟩ frag f ← str (○ (_ ─✴[ demand ] M Q)) (m st σ₄ ×⟨ ⊎-comm σ₃ ⟩ inj (frag f))
      case ⊎-assoc (⊎-comm σ₅) σ₆ of λ where
        (_ , σ₇ , demand σ₈) → f px (⊎-comm σ₈) st' (⊎-comm σ₇)

  
module StateOps {unit : T} (tt : V unit ε) where

  get : ∀ {a} → ∀[ ○ (Just a) ⇒ M (V a ✴ Just unit) ]
  get (frag ptr) (lift st σ₁) σ = do
    -- p ← ●-update get' (lift (snd ptr ×⟨ {!!} , {!!} ⟩ st) σ₃) -- ●-update get' (lift ((snd ptr) ×⟨ ⊎-idˡ , ⊎-comm σ₃ ⟩ st) σ₄)
    {!!}
    -- where
    --   get' : ∀ {a} → ∀[ Π₂ (Just a) ✴ Cells ⇒ ⟰ (Cells ✴ Π₂ (V a ✴ Just unit)) ]
    --   get' (snd refl ×⟨ σ₁ , σ₂ ⟩ cs) com with ⊎-id⁻ˡ σ₁
    --   get' (snd refl ×⟨ σ₁ , consˡ σ₂ ⟩ cs) com | refl = {!!}
    --   get' (snd refl ×⟨ σ₁ , consʳ σ₂ ⟩ cs) com | refl = {!!}
