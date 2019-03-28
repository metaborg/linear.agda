module Sessions.Semantics.Expr-01 where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

-- The command structure is the justification of changes made to the session context.
data Cmd : SCtx → Set where
  send    : ∀ {a α}   → ∀[ (Chan (a ⅋ α) ✴ Val a) ⇒ Cmd ]
  receive : ∀ {a α}   → ∀[ Chan (a ⊗ α) ⇒ Cmd ]
  close   :             ∀[ Chan end ⇒ Cmd ]
  fork    : ∀ {α b}   → ∀[ Closure (chan α) b ⇒ Cmd ]

δ : ∀ {Δ} → Cmd Δ → Pred SCtx 0ℓ
δ (send {α = α} _)    = Chan (α .force)
δ (receive {a} {α} _) = Chan (α .force) ✴ Val a 
δ (close _)           = Emp
δ (fork {α} _)        = Chan (α ⁻¹)

data F : Pt SCtx 0ℓ where
  pure   : ∀ {P}   → ∀[ P ⇒ F P ] 
  impure : ∀ {P}   → ∀[ ∃[ Cmd ]✴ (λ c → δ c ─✴ F P) ⇒ F P ]

module Free where

  f-return : ∀ {P} → ∀[ P ⇒ F P ]
  f-return = pure

  -- There is some intuition here, but it is hard to find...
  -- consider: ∀[ (f : P ─✴ F Q) ⇒ (g : F P ─✴ F Q) ]
  -- Then the resource typing says that you need as much resource to construct F Q from F P,
  -- as you need to construct F Q from P.
  f-bind : ∀ {P Q} → ∀[ (P ─✴ F Q) ⇒ (F P ─✴ F Q) ]
  f-bind f (pure x)     = f x
  f-bind {P} {Q} {Φu} f {Φₚ} (impure (_×⟨_⟩_ {Φcmd} {Φk} cmd dj k)) {Φ} s =
    impure (cmd ×⟨ sep ⟩ λ {u'} r → λ {Ψ} sup →
      let (Φ? , sip , sap) = ⊎-assoc (⊎-comm sop) sup in
      f-bind f (k r sip) sap  )
    where
      Φk' = proj₁ $ ⊎-assoc dj (⊎-comm s)
      prf = proj₂ $ ⊎-assoc dj (⊎-comm s)

      sep : Φcmd ⊎ Φk' ≣ Φ
      sep = proj₂ prf

      sop : Φk ⊎ Φu ≣ Φk'
      sop = proj₁ prf

  -- put the arguments in the right order
  syntax f-bind f p s = p split s bind f

  send! : ∀ {α} → ∀[ Chan (a ⅋ α) ✴ Val a ⇒ F (Chan (α .force)) ]
  send! args =
    impure (send args ×⟨ ⊎-identityʳ refl ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  receive! : ∀ {α} → ∀[ Chan (a ⊗ α) ⇒ F (Chan (α .force) ✴ Val a) ]
  receive! args =
    impure (receive args ×⟨ ⊎-identityʳ refl ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  close! : ∀[ Chan end ⇒ F Emp ]
  close! args =
    impure (close args ×⟨ ⊎-identityʳ refl ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  fork! : ∀[ Closure (chan α) b ⇒ F (Chan (α ⁻¹)) ]
  fork! args =
    impure (fork args ×⟨ ⊎-identityʳ refl ⟩ λ v s →
      subst (F _) (⊎-identity⁻ˡ s) (pure v))

  {-# TERMINATING #-}
  eval : Exp a Γ → ∀[ Env Γ ⇒ F (Val a) ]
  eval (var refl) (cons (px ×⟨ sep ⟩ [] refl))
    rewrite ⊎-identity⁻ʳ sep = f-return px

  eval (unit x) ([] refl) =
    f-return (tt refl)

  eval (λₗ a x) env =
    f-return (clos (closure x env))

  eval (app (f ×⟨ Γ≺ ⟩ e)) env =
    -- split the environment in two (disjoint) parts according to the Γ separation
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    eval f E₁ split (⊎-comm E≺) bind λ where
      (clos (closure body closure-env)) clo◆E₂ →
        eval e E₂ split (⊎-comm clo◆E₂) bind λ where
          v v◆E₂ →
            let closure' = cons (v ×⟨ ⊎-comm v◆E₂ ⟩ closure-env)
            in eval body closure'

  eval (pair (px ×⟨ Γ≺ ⟩ qx)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    eval px E₁ split (⊎-comm E≺) bind λ v v◆E₁ →
      eval qx E₂ split (⊎-comm v◆E₁) bind λ w dj →
        f-return (pair (v ×⟨ dj ⟩ w))

  eval (letpair (p IsSep.×⟨ Γ≺ ⟩ k)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    (eval p E₁) split (⊎-comm E≺) bind λ where
      (pair (v ×⟨ v◆w ⟩ w)) pr◆E₂ →
        let -- extend the environment with the two values
            (Φ , sip , sop) = ⊎-assoc v◆w (⊎-comm pr◆E₂)
            Eₖ = cons (v ×⟨ sop ⟩ (cons (w ×⟨ sip ⟩ E₂)))
        in eval k Eₖ

  eval (send (e IsSep.×⟨ Γ≺ ⟩ ch)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    (eval ch E₂) split E≺ bind λ where
    (chan φ) φ◆E₁ →
      (eval e E₁) split (⊎-comm φ◆E₁) bind λ v φ◆v →
      (send! (φ ×⟨ φ◆v ⟩ v)) split (⊎-identityˡ refl) bind λ ch s →
      f-return (chan (subst (Chan _) (⊎-identity⁻ˡ s) ch))

  eval (recv e) env =
    (eval e env) split ⊎-identityˡ refl bind λ where
      (chan ch) ε◆ch → receive! ch split ε◆ch bind λ a×b s →
        f-return $ subst (Val _) (⊎-identity⁻ˡ s) $
          pair (⟨ chan ⟨✴⟩ id ⟩ a×b)  

  eval (fork e) env =
    eval e env split ⊎-identityˡ refl bind λ where
      (clos clo) s → fork! clo split s bind λ φ s →
        f-return $ subst (Val _) (⊎-identity⁻ˡ s) (chan φ)

  eval (terminate e) env =
    eval e env split ⊎-identityˡ refl bind λ where
      (chan ch) ε◆sh → close! ch split ε◆sh bind λ where
        refl → f-return ∘ tt ∘ ε⊎ε
