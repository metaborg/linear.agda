-- | In this interpreter for expressions we interpret communication and threading in the free monad.
-- The interpretation is well-typed-by-construction in the sense that computed values
-- match the expression typ *and* linear usage of the session context is *enforced*.
--
-- We do not bother trying to hide splitting in the implementations here.
module Sessions.Semantics.Expr-01 where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

-- The command structure is the justification of changes made to the session context.
data Cmd : Pred SCtx 0ℓ where
  send    : ∀ {a α}   → ∀[ (Just (a ! α) ✴ Val a) ⇒ Cmd ]
  receive : ∀ {a α}   → ∀[ Just (a ¿ α) ⇒ Cmd ]
  close   :             ∀[ Just end ⇒ Cmd ]
  fork    : ∀ {α b}   → ∀[ Closure (chan α) b ⇒ Cmd ]

δ : ∀ {Δ} → Cmd Δ → Pred SCtx 0ℓ
δ (send {α = α} _)    = Just (α .force)
δ (receive {a} {α} _) = Just (α .force) ✴ Val a 
δ (close _)           = Emp
δ (fork {α} _)        = Just (α ⁻¹)

mutual
  Cont : ∀ {Δ} → Cmd Δ → Pred SCtx 0ℓ → Pred SCtx 0ℓ
  Cont c P = δ c ─✴ F P -- P ─✴ Q = \ i → ∀ {j k} → i ⊎ j ≣ k → P j → Q k

  data F : Pt SCtx 0ℓ where
    pure   : ∀ {P}   → ∀[ P ⇒ F P ] 
    impure : ∀ {P}   → ∀[ ∃[ Cmd ]✴ (λ c → Cont c P) ⇒ F P ]

module Free where

  f-return : ∀ {P} → ∀[ P ⇒ F P ]
  f-return = pure

  f-map : ∀ {P Q} → ∀[ (P ─✴ Q) ⇒ (F P ─✴ F Q) ]
  f-map f (pure x) σ                  = pure (f x σ)
  f-map f (impure (cmd ×⟨ σ₁ ⟩ κ)) σ₂ =
    let (Φ , eq₁ , eq₂) = ⊎-assoc σ₁ (⊎-comm σ₂) in
    impure (cmd ×⟨ eq₁ ⟩ (λ r σ₃ →
      let (Φ' , eq₃ , eq₄) = ⊎-assoc (⊎-comm eq₂) σ₃ in
      f-map f (κ r eq₄) eq₃))

  f-join : ∀ {P} → ∀[ F (F P) ⇒ F P ]
  f-join (pure fp)  = fp
  f-join (impure (cmd ×⟨ σ ⟩ κ)) = impure (cmd ×⟨ σ ⟩ λ r σ' → f-join (κ r σ'))

  f-bind : ∀ {P Q} → ∀[ (P ─✴ F Q) ⇒ (F P ─✴ F Q) ]
  f-bind f fp = f-join ∘ f-map f fp

  -- put the arguments in the right order
  syntax f-bind f p s = p ⟪ s ⟫= f

  send! : ∀ {α} → ∀[ Just (a ! α) ✴ Val a ⇒ F (Just (α .force)) ]
  send! args =
    impure (send args ×⟨ ⊎-identityʳ ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  receive! : ∀ {α} → ∀[ Just (a ¿ α) ⇒ F (Just (α .force) ✴ Val a) ]
  receive! args =
    impure (receive args ×⟨ ⊎-identityʳ ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  close! : ∀[ Just end ⇒ F Emp ]
  close! args =
    impure (close args ×⟨ ⊎-identityʳ ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  fork! : ∀[ Closure (chan α) b ⇒ F (Just (α ⁻¹)) ]
  fork! args =
    impure (fork args ×⟨ ⊎-identityʳ ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  {-# TERMINATING #-}
  eval : Exp a Γ → ∀[ Env Γ ⇒ F (Val a) ]
  eval (var refl) (cons (px ×⟨ sep ⟩ nil ))
    rewrite ⊎-identity⁻ʳ sep = f-return px

  eval (unit x) nil =
    f-return (tt refl)

  eval (λₗ a x) env =
    f-return (clos (closure x env))

  eval (app (f ×⟨ Γ≺ ⟩ e)) env =
    -- split the environment in two (disjoint) parts according to the Γ separation
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    eval f E₁ ⟪ ⊎-comm E≺ ⟫= λ where
      (clos (closure body closure-env)) clo◆E₂ →
        eval e E₂ ⟪ ⊎-comm clo◆E₂ ⟫= λ where
          v v◆E₂ →
            let closure' = cons (v ×⟨ ⊎-comm v◆E₂ ⟩ closure-env)
            in eval body closure'

  eval (pairs (px ×⟨ Γ≺ ⟩ qx)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    eval px E₁ ⟪ ⊎-comm E≺ ⟫= λ v v◆E₁ →
      eval qx E₂ ⟪ ⊎-comm v◆E₁ ⟫= λ w dj →
        f-return (pairs (v ×⟨ dj ⟩ w))

  eval (letpair (p ×⟨ Γ≺ ⟩ k)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    (eval p E₁) ⟪ ⊎-comm E≺ ⟫= λ where
      (pairs (v ×⟨ v◆w ⟩ w)) pr◆E₂ →
        let -- extend the environment with the two values
          _ , sip , sop = ⊎-assoc v◆w (⊎-comm pr◆E₂)
          Eₖ = cons (v ×⟨ sip ⟩ cons (w ×⟨ sop ⟩ E₂))
        in eval k Eₖ

  eval (send (e ×⟨ Γ≺ ⟩ ch)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    (eval ch E₂) ⟪ E≺ ⟫= λ where
    (chan φ) φ◆E₁ →
      (eval e E₁) ⟪ ⊎-comm φ◆E₁ ⟫= λ v φ◆v →
      (send! (φ ×⟨ φ◆v ⟩ v)) ⟪ ⊎-identityˡ ⟫= λ ch s →
      f-return (chan (subst (Just _) (⊎-identity⁻ˡ s) ch))

  eval (recv e) env =
    (eval e env) ⟪ ⊎-identityˡ ⟫= λ where
      (chan ch) ε◆ch → receive! ch ⟪ ε◆ch ⟫= λ a×b s →
        f-return $ subst (Val _) (⊎-identity⁻ˡ s) $
          pairs (⟨ chan ⟨✴⟩ id ⟩ a×b)  

  eval (fork e) env =
    eval e env ⟪ ⊎-identityˡ ⟫= λ where
      (clos clo) s → fork! clo ⟪ s ⟫= λ φ s →
        f-return $ subst (Val _) (⊎-identity⁻ˡ s) (chan φ)

  eval (terminate e) env =
    eval e env ⟪ ⊎-identityˡ ⟫= λ where
      (chan ch) ε◆sh → close! ch ⟪ ε◆sh ⟫= λ where
        refl → f-return ∘ tt ∘ ε⊎ε
