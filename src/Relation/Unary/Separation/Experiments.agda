

  -- A predicate transformer allowing one to express that
  -- some value definitely does /not/ own some resource
  infixl 9 _◇_
  data _◇_ {p} (P : SPred p) (Φᵢ : Carrier) : SPred (p ⊔ a) where
    ⟪_,_⟫ : ∀ {Φₚ Φ} → P Φₚ → Φᵢ ⊎ Φₚ ≣ Φ → (P ◇ Φᵢ) Φ

  -- | This gives another wand like thing

  module _ {p q} (P : SPred p) (Q : SPred q) where
    infixr 8 _◇─_
    _◇─_ : SPred (p ⊔ q ⊔ a)
    _◇─_ Φᵢ = ∀[ P ◇ Φᵢ ⇒ Q ]

  module _ {p q} {P : SPred p} {Q : SPred q} where
    pair : ε[ P ◇─ (Q ◇─ P ✴ Q) ]
    pair ⟪ px , σ₁ ⟫ ⟪ qx , σ₂ ⟫ rewrite ⊎-id⁻ˡ σ₁ = px ×⟨ σ₂ ⟩ qx

  module _ {p} {P : SPred p} where
    ◇-ε : ∀[ P ◇ ε ⇒ P ]
    ◇-ε ⟪ px , σ ⟫ rewrite ⊎-id⁻ˡ σ = px


    -- pure : ∀ {p q} {P : SPred p} {Q : SPred q} → (P ε → Q Φ) → (P ─✴ Q) Φ
    -- pure f px = {!!}
    -- -- pure = {!!}
    -- a pure wand is a resource-polymorphic function
    -- unwand : ε[ P ─✴ Q ] → ∀[ P ⇒ Q ]
    -- unwand f p = f p ⊎-idˡ
    
    -- ✴-pure : ∀ {p q} {P : SPred p} {Q : SPred q} → (∀ {Φ} → P Φ → ε ⊎ Φ ≣ Φ → Q Φ) → ε[ P ─✴ Q ]
    -- ✴-pure f px σ rewrite ⊎-id⁻ˡ σ = f px ⊎-idˡ

    -- ✴-flip : ∀ {p q r} {P : SPred p} {Q : SPred q} {R : SPred r} → ε[ (P ─✴ (Q ─✴ R)) ─✴ (Q ─✴ (P ─✴ R)) ]
    -- ✴-flip {P = P} {Q} {R} = 
    --   ✴-pure {P = P ─✴ (Q ─✴ R)} {Q = Q ─✴ (P ─✴ R)} λ f σ₁ q σ₂ p σ₃ → 
    --   let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) σ₃ in f p σ₄ q (⊎-comm σ₃)

  -- ─[id] : ∀ {p} {P : Pred _ p} → ε[ P ─✴ P ]
  -- ─[id] px σ rewrite ⊎-id⁻ˡ σ = px
