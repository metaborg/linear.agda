-- | We move the environment into the monad, getting rid of explicit env-splits.
-- To accomplish this we introduces `frame` as a primitive.
module Sessions.Semantics.Expr-02 where

open import Prelude
open import Data.Fin

open import Relation.Unary.PredicateTransformer hiding (_⊔_)

open import Sessions.Syntax.Types
open import Sessions.Syntax.Values
open import Sessions.Syntax.Expr

open import Sessions.Semantics.Expr-01 using (Cmd; F; module Free; pure; impure; Cont) public

module M where

  M : LCtx → LCtx → Pred SCtx 0ℓ → Pred SCtx 0ℓ
  M Γ₁ Γ₂ P = Env Γ₁ ─✴ F (Env Γ₂ ✴ P) 

  return : ∀ {P} → ∀[ P ⇒ M Γ Γ P ]
  return px e s = pure (e ×⟨ ⊎-comm s ⟩ px)

  ibind : ∀ {P Q} → ∀[ (P ─✴ M Γ₂ Γ₃ Q) ⇒ (M Γ₁ Γ₂ P ─✴ M Γ₁ Γ₃ Q) ]
  ibind f mp σ₁ env σ₂ =
    let
      _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
      f[e✴px]       = mp env σ₄
    in Free.f-bind (λ where
      (env ×⟨ σ₅ ⟩ px) σ₆ →
        let _ , σ₇ , σ₈ = ⊎-assoc σ₅ (⊎-comm σ₆)
        in f px (⊎-comm σ₈) env (⊎-comm σ₇)) f[e✴px] σ₃

  _=<<_ :  ∀ {P Q} → ∀[ P ⇒ M Γ₂ Γ₃ Q ] → ∀[ M Γ₁ Γ₂ P ⇒ M Γ₁ Γ₃ Q ]
  f =<< mp = ibind (λ px σ → case ⊎-id⁻ˡ σ of λ where refl → f px ) mp ⊎-idˡ 

  _>>=_ : ∀ {Φ} {P Q} → M Γ₁ Γ₂ P Φ → ∀[ P ⇒ M Γ₂ Γ₃ Q ] → M Γ₁ Γ₃ Q Φ
  mp >>= f = f =<< mp

  str : ∀ {P Q} → ∀[ M Γ₁ Γ₂ P ✴ Q ⇒ M Γ₁ Γ₂ (P ✴ Q)]
  str (mp ×⟨ σ₁ ⟩ qx) =
    ibind (λ px σ₃ env σ₄ →
      Free.f-return (env ×⟨ ⊎-comm σ₄ ⟩ px ×⟨ ⊎-comm σ₃ ⟩ qx)) mp (⊎-comm σ₁)

  lift-f : ∀ {P} → ∀[ F P ⇒ M ε ε P ]
  lift-f px nil σ = Free.f-map (λ px σ' → nil ×⟨ σ' ⟩ px) px (⊎-comm σ)

  -- syntax bind f p s = p split s bind f
  syntax ibind f p s = p ⟪ s ⟫= f

  frame : ∀ {P} → Γ₁ ⊎ Γ₃ ≣ Γ₂ → ∀[ M Γ₁ ε P ⇒ M Γ₂ Γ₃ P ]
  frame sep c env s =
    let
      (E₁ ×⟨ E≺ ⟩ E₂) = env-split sep env
      (Φ , eq₁ , eq₂) = ⊎-assoc E≺ (⊎-comm s)
    in ibind
      (λ px s' → λ where nil s'' → pure $ E₂ ×⟨ subst (_ ⊎ _ ≣_) (⊎-id⁻ʳ s'') s' ⟩ px)
      c eq₂ E₁ (⊎-comm eq₁)

  ask : ε[ M Γ ε (Allstar Val Γ) ]
  ask env σ = Free.f-return (nil ×⟨ σ ⟩ env)

  prepend : ∀[ Env Γ₁ ⇒ M Γ₂ (Γ₁ ∙ Γ₂) Emp ]
  prepend env₁ env₂ s = pure $ env-∙ (env₁ ×⟨ s ⟩ env₂) ×⟨ ⊎-idʳ ⟩ empty

  append : ∀[ Env Γ₁ ⇒ M Γ₂ (Γ₂ ∙ Γ₁) Emp ]
  append env₁ env₂ s = pure $ env-∙ (env₂ ×⟨ ⊎-comm s ⟩ env₁) ×⟨ ⊎-idʳ ⟩ empty

module _ where
  open M

  {-# TERMINATING #-}
  eval′ : Exp a Γ → ε[ M Γ ε (Val a) ]
  eval′ (var refl) = do
    cons (v ×⟨ σ ⟩ nil) ← ask
    case ⊎-id⁻ʳ σ of λ where
      refl → return v

  eval′ unit =
    return tt

  eval′ (λₗ a e) = do
    env ← ask
    return (clos (closure e env)) 

  eval′ (app (f ×⟨ Γ≺ ⟩ e)) = do
    clos (closure body env) ← frame Γ≺ (eval′ f)
    v ×⟨ σ ⟩ env            ← str {Q = Env _} (eval′ e ×⟨ ⊎-idˡ ⟩ env)
    empty                   ← append (cons (v ×⟨ σ ⟩ env))
    eval′ body

  eval′ (pairs (fst ×⟨ Γ≺ ⟩ snd)) = do
    v ← frame Γ≺ (eval′ fst)
    w ← str (eval′ snd ×⟨ ⊎-idˡ ⟩ v)
    return (pairs (✴-swap w))

  eval′ (letpair (e ×⟨ Γ≺ ⟩ body)) = do
    pairs (px ×⟨ σ ⟩ qx) ← frame Γ≺ (eval′ e)
    let env'             = cons (px ×⟨ σ ⟩ singleton qx)
    empty                ← prepend env'
    eval′ body

  eval′ (send (e ×⟨ Γ≺ ⟩ ch)) = do
    v                 ← frame Γ≺ (eval′ e)
    (chan φ ×⟨ σ ⟩ v) ← str (eval′ ch ×⟨ ⊎-idˡ ⟩ v)
    r                 ← lift-f (Free.send! (φ ×⟨ σ ⟩ v))
    return (chan r)

  eval′ (recv e) = do
    chan φ      ← eval′ e
    φ' ×⟨ σ ⟩ v ← lift-f (Free.receive! φ)
    return (pairs ((chan φ') ×⟨ σ ⟩ v))

  eval′ (fork e) = do
    clos κ ← eval′ e
    φ      ← lift-f (Free.fork! κ)
    return (chan φ)

  eval′ (terminate e) = do
    chan φ ← eval′ e
    empty  ← lift-f (Free.close! φ)
    return tt

  eval : Exp a ε → F (Val a) ε
  eval e =
    Free.f-map
      (λ where (nil ×⟨ σ₁ ⟩ qx) σ₂ → subst (Val _) (trans (⊎-id⁻ˡ σ₁) (⊎-id⁻ˡ σ₂)) qx)
      (eval′ e nil ⊎-idˡ) ⊎-idˡ

  -- The version using the internal bind instead

  -- ieval : Exp a Γ → M Γ ε (Val a) ε
  -- ieval (var refl) = ask ⟪ ? ⟫= λ where
  --   (cons (v ×⟨ σ₁ ⟩ nil)) σ₂ →
  --     case trans (⊎-id⁻ʳ σ₁) (⊎-id⁻ˡ σ₂) of λ where
  --       refl → return v

  -- ieval unit =
  --   return tt

  -- ieval (λₗ a e) =
  --   ask ⟪ ? ⟫= λ env σ →
  --     clos (closure e (subst (Env _) (⊎-id⁻ˡ σ) env))

  -- ieval (app (f ×⟨ Γ≺ ⟩ e)) =
  --   frame Γ≺ (ieval f) ⟪ ⊎-idʳ ⟫= λ where
  --     (clos (closure body closure-env)) s → ieval e ⟪ ⊎-comm s ⟫= λ where
  --       v σ₁ → append (singleton v) ⟪ σ₁ ⟫= λ where
  --         refl σ₂ → append closure-env ⟪ ⊎-comm σ₂ ⟫= λ where
  --           refl σ₃ → subst (M _ _ _) (⊎-id⁻ˡ σ₃) (ieval body)

  -- ieval (pairs (fst ×⟨ Γ≺ ⟩ snd)) =
  --   frame Γ≺ (ieval fst) ⟪ ⊎-idˡ ⟫= λ where
  --     v σ₁ → ieval snd ⟪ ⊎-comm σ₁ ⟫= λ where
  --       w σ₂ → return (pairs (v ×⟨ σ₂ ⟩ w))

  -- ieval (letpair (e ×⟨ Γ≺ ⟩ body)) =
  --   frame Γ≺ (ieval e) ⟪ ⊎-idˡ ⟫= λ where
  --     (pairs (px ×⟨ σ₁ ⟩ qx)) σ₂ →
  --       let env' = cons (px ×⟨ σ₁ ⟩ singleton qx)
  --       in prepend env' ⟪ σ₂ ⟫= λ where
  --       refl σ₃ → subst (M _ _ _) (⊎-id⁻ˡ σ₃) (ieval body)

  -- ieval (send (e ×⟨ Γ≺ ⟩ ch)) =
  --   frame Γ≺ (ieval e) ⟪ ⊎-idˡ ⟫= λ where
  --     v σ₁ → ieval ch ⟪ ⊎-comm σ₁ ⟫= λ where
  --       (chan φ) σ₂ → lift-f (Free.send! (φ ×⟨ ⊎-comm σ₂ ⟩ v)) ⟪ ⊎-idˡ ⟫= λ where
  --         v σ₃ → subst (M _ _ _) (⊎-id⁻ˡ σ₃) (return (chan v))

  -- ieval (recv e) =
  --   ieval e ⟪ ⊎-idˡ ⟫= λ where
  --     (chan φ) σ₁ → lift-f (Free.receive! φ) ⟪ σ₁ ⟫= λ where
  --       φ✴v σ₃ → subst (M _ _ _) (⊎-id⁻ˡ σ₃) (return (pairs (⟨ chan ⟨✴⟩ id ⟩ φ✴v)))

  -- ieval (fork e) =
  --   ieval e ⟪ ⊎-idˡ ⟫= λ where
  --     (clos κ) σ₁ → lift-f (Free.fork! κ) ⟪ σ₁ ⟫= λ where
  --       φ σ₂ → subst (M _ _ _) (⊎-id⁻ˡ σ₂) (return (chan φ))

  -- ieval (terminate e) =
  --   ieval e ⟪ ⊎-idˡ ⟫= λ where
  --     (chan φ) σ₁ → lift-f (Free.close! φ) ⟪ σ₁ ⟫=  λ where
  --       refl σ₂ → subst (M _ _ _) (⊎-id⁻ˡ σ₂) (return (tt refl))
