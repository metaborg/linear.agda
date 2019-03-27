module Sessions.Semantics.LinearState where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

-- (A ─✴ B) Σ = ∀ Σ' → Σ ◆ Σ' → A Σ' → B (Σ ∙ Σ')
-- (A ─◆ B) Σ = A Σ → B Σ' × Σ' ◆ Σ
--   ▻ Or, perhaps (all state extensions are disjoint): (A ─◆ B) Σ = A Σ → ∃ B 

-- The command structure is the justification of changes made to the session context.
data Cmd : SCtx → Set where
  send    : ∀ {a α}   → ∀[ (Chan (a ⅋ α) ✴ Val a) ⇒ Cmd ]
  receive : ∀ {a α}   → ∀[ Chan (a ⊗ α) ⇒ Cmd ]
  close   :             ∀[ Chan end ⇒ Cmd ]

-- D : ∀ {Φ} → Cmd Φ → SCtx
-- D {Φ} (send {a} {α} _)        = α .force ∷ [] 
-- D {Φ} (receive {a} {α} {b} x) = {!α .force ∷ b ∷ !}
-- D {Φ} (close x) = {!!}

δ : ∀ {Δ} → Cmd Δ → Pred SCtx 0ℓ
δ (send {α = α} _)    = Chan (α .force)
δ (receive {a} {α} _) = Chan (α .force) ✴ Val a 
δ (close _)           = U

data F : Pt SCtx 0ℓ where
  pure   : ∀ {P}   → ∀[ P ⇒ F P ] 
  impure : ∀ {P}   → ∀[ ∃[ Cmd ]✴ (λ c → δ c ─✴ F P) ⇒ F P ]

send! : ∀ {α} → ∀[ Chan (a ⅋ α) ✴ Val a ⇒ F (Chan (α .force)) ]
send! args =
  impure ((send args) ×⟨ ⊎-identityʳ refl ⟩ λ v s → subst (F _) (⊎-identity⁻ˡ s) (pure v))

■_ : ∀ {ℓ} → Pt SCtx ℓ
■ P = λ i → ∀ {j} → P j

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

  {-# TERMINATING #-}
  eval : Exp a Γ → ∀[ Env Γ ⇒ F (Val a) ]
  eval (var refl) (cons (px ×⟨ sep ⟩ [] refl))
    rewrite ⊎-identity⁻ʳ sep = f-return px

  eval (unit x) ([] refl) =
    f-return (tt refl)

  eval (λₗ a x) env =
    f-return (clos x env)

  eval (app (f ×⟨ Γ≺ ⟩ e)) env =
    -- split the environment in two (disjoint) parts according to the Γ separation
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    f-bind (λ where
      (clos body closure) clo◆E₂ →
        f-bind (λ where
          v v◆E₂ →
            let closure' = cons (v ×⟨ ⊎-comm v◆E₂ ⟩ closure)
            in eval body closure')
          (eval e E₂)
          (⊎-comm clo◆E₂))
      (eval f E₁)
      (⊎-comm E≺)

  eval (pair (px ×⟨ Γ≺ ⟩ qx)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    f-bind (λ v v◆E₁ →
      f-bind (λ w dj →
        f-return (pair (v ×⟨ dj ⟩ w)))
        (eval qx E₂)
        (⊎-comm v◆E₁))
      (eval px E₁)
      (⊎-comm E≺)

  eval (letpair (p IsSep.×⟨ Γ≺ ⟩ k)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    f-bind (λ where
        (pair (v ×⟨ v◆w ⟩ w)) pr◆E₂ →
          let
            -- extend the environment with the two values
            (Φ , sip , sop) = ⊎-assoc v◆w (⊎-comm pr◆E₂)
            Eₖ = cons (v IsSep.×⟨ sop ⟩ (cons (w IsSep.×⟨ sip ⟩ E₂)))
          in eval k Eₖ)
      (eval p E₁)
      (⊎-comm E≺)

  eval (send (e IsSep.×⟨ Γ≺ ⟩ ch)) env =
    let (E₁ ×⟨ E≺ ⟩ E₂) = env-split Γ≺ env in
    f-bind (λ where
      (chan φ) φ◆E₁ →
        f-bind (λ v φ◆v →
          f-bind (λ ch s →
            f-return (chan (subst (Chan _) (⊎-identity⁻ˡ s) ch)))
            (send! (φ IsSep.×⟨ φ◆v ⟩ v))
            (⊎-identityˡ refl))
          (eval e E₁)
          (⊎-comm φ◆E₁))
      (eval ch E₂)
      E≺

  eval (recv e) = {!!}

  eval (fork e) = {!!}

  eval (terminate e) = {!!}
