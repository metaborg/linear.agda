module Examples where

open import Prelude
open import Sessions.Syntax

module _ where
  open import Relation.Ternary.Separation.Construct.List Type

  lets : ∀[ Exp a ⇒ (a ∷_) ⊢ Exp b ─✴ Exp b ]
  app (lets e₁) e₂ σ = ap (lam _ e₂ ×⟨ ⊎-comm σ ⟩ e₁)

  -- The example from section 2.1 of the paper
  ex₁ : Exp unit ε
  ex₁ =
    letpair (mkchan (unit ! end) ×⟨ ⊎-idʳ ⟩ (
    lets (fork
      (lam unit
        (letpair (recv (var refl) ×⟨ consʳ (consˡ []) ⟩
          letunit (letunit (var refl ×⟨ ⊎-∙ ⟩ var refl) ×⟨ consʳ ⊎-idʳ ⟩
            (terminate (var refl))))))) $⟨ consʳ (consˡ []) ⟩
    (lets (send (unit ×⟨ ⊎-idˡ ⟩ var refl)) $⟨ ⊎-comm ⊎-∙ ⟩
      letunit (var refl ×⟨ consʳ ⊎-∙ ⟩ terminate (var refl)))))

module _ where
  open import Sessions.Semantics.Expr
  open import Sessions.Semantics.Process as P hiding (main)
  open import Relation.Ternary.Separation.Construct.Market
  open import Relation.Ternary.Separation.Monad.Error

  pool₁ : ∃ λ Φ → Except Exc (● St) Φ
  pool₁ = start 1000 (P.main comp)
    where
      comp = app (runReader nil) (eval 1000 ex₁) ⊎-idˡ

open import IO
open import Data.String.Base using (_++_)
open import Codata.Musical.Notation
open import Debug.Trace
open import Data.Sum
open import Relation.Ternary.Separation.Monad.Error

main = run $ ♯ (putStrLn "Hello, World!")
    >> ♯ (♯ putStrLn result
    >> ♯ putStrLn "done")
  where
  result = case pool₁ of λ where
             (ty , ExceptT.partial (inj₁ e)) → "fail"
             (ty , ExceptT.partial (inj₂ v)) → "ok"
