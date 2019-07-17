{-# OPTIONS --without-K --rewriting #-}

-- A separation algebra.
-- Axiomatization based on
-- "A fresh look at Separation Algebras and Share Accounting" (Dockins et al)
module Relation.Unary.Separation where

open import Function
open import Level

open import Data.Unit using (tt)
open import Data.Product hiding (map)
open import Data.List.Relation.Ternary.Interleaving.Propositional hiding (map)
open import Data.List.Relation.Binary.Equality.Propositional

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Algebra
open import Algebra.FunctionProperties.Core

record RawSep {a} (Carrier : Set a) : Set (suc a) where

  SPred : (ℓ : Level) → Set _
  SPred ℓ = Pred Carrier ℓ

  field
    _⊎_≣_ : (Φ₁ Φ₂ : Carrier) → SPred a

  -- we can see the three point relation as a predicate on the carrier
  _⊎_ = _⊎_≣_

  -- buy one, get a preorder for free
  _≤_ : Rel Carrier _
  Φ₁ ≤ Φ = ∃ λ Φ₂ → (Φ₁ ⊎ Φ₂) Φ

  -- separating conjunction
  infixr 10 _×⟨_⟩_
  record Conj {p q} (P : SPred p) (Q : ∀ {Φ} → P Φ → SPred q) Φ : Set (p ⊔ q ⊔ a) where
    inductive
    constructor _×⟨_⟩_
    field
      {Φₗ Φᵣ} : Carrier

      px  : P Φₗ
      sep : (Φₗ ⊎ Φᵣ) Φ
      qx  : Q px Φᵣ

  infixr 9 ∃[_]✴_
  ∃[_]✴_ = Conj

  infixr 9 _✴_
  _✴_ : ∀ {p q} → SPred p → SPred q → SPred (p ⊔ q ⊔ a)
  P ✴ Q = ∃[ P ]✴ const Q

  -- | Separating implication / magic is what you wand

  infixr 8 _─✴_
  _─✴_ : ∀ {p q} (P : SPred p) (Q : SPred q) → SPred (p ⊔ q ⊔ a)
  P ─✴ Q = λ Φᵢ → ∀ {Φₚ} → P Φₚ → ∀[ Φᵢ ⊎ Φₚ ⇒ Q ]

  _─✴′_ : ∀ {p q} (P : SPred p) (Q : SPred q) → SPred (p ⊔ q ⊔ a)
  P ─✴′ Q = λ Φᵢ → ∀ {Φₚ Φ} → (P Φₚ × Φᵢ ⊎ Φₚ ≣ Φ) → Q Φ

  -- | The update modality

  ⤇ : ∀ {p} → SPred p → SPred (a ⊔ p)
  ⤇ P Φᵢ = ∀ {Φⱼ Φₖ} → Φᵢ ⊎ Φⱼ ≣ Φₖ → ∃₂ λ Φₗ Φ → Φₗ ⊎ Φⱼ ≣ Φ × P Φₗ
    -- Φᵢ is what we own, Φⱼ is an arbitrary frame.
    -- We may update Φᵢ as long as we do not disturb the framing

  infixr 8 _==✴_
  _==✴_ : ∀ {p q} → (P : SPred p) (Q : SPred q) → SPred (p ⊔ q ⊔ a)
  P ==✴ Q = P ─✴ (⤇ Q)

  module Diamond where

    -- _◆_ : Rel Carrier _
    -- _◆_ = ∃ _⊎_

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
      mkPair : ∀[ P ⇒ (Q ◇─ P ✴ Q) ]
      mkPair px ⟪ qx , σ ⟫ = px ×⟨ σ ⟩ qx

record IsSep {ℓ₁} {A} (s : RawSep {ℓ₁} A) : Set ℓ₁ where
  open RawSep s

  field
    -- ⊎-functional   : ∀ {Φ₁ Φ₂ Φ Φ'}   → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ⊎ Φ₂ ≣ Φ' → Φ ≈ Φ'
    -- ⊎-cancellative : ∀ {Φ₁ Φ₁' Φ₂}    → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₁' ⊎ Φ₂ ⇒ (λ _ → Φ₁ ≈ Φ₁') ]
    ⊎-comm         : ∀ {Φ₁ Φ₂}        → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₂ ⊎ Φ₁ ]
    ⊎-assoc        : ∀ {Φ₁ Φ₂ Φ₃ Φ Ψ} → Φ₁ ⊎ Φ₂ ≣ Φ → Φ ⊎ Φ₃ ≣ Ψ →
                                        ∃ λ Φ₄ → Φ₂ ⊎ Φ₃ ≣ Φ₄ × Φ₁ ⊎ Φ₄ ≣ Ψ

  variable
    Φ₁ Φ₂ Φ₃ Φ : A

  -- mapping
  module _ {p q p' q'}
    {P : SPred p} {Q : SPred q} {P' : SPred p'} {Q' : SPred q'} where

    ⟨_⟨✴⟩_⟩ : (P ⊆ P') → (Q ⊆ Q') → P ✴ Q ⊆ P' ✴ Q'
    ⟨_⟨✴⟩_⟩ f g (px ×⟨ sep ⟩ qx) = (f px) ×⟨ sep ⟩ (g qx)

  -- commute product
  module _ {p q}
    {P : SPred p} {Q : SPred q} where
    ✴-swap : ∀[ (P ✴ Q) ⇒ (Q ✴ P) ]
    ✴-swap (px ×⟨ σ ⟩ qx) = qx ×⟨ ⊎-comm σ ⟩ px

  module _ {p q} {P : SPred p} {Q : SPred q} where
    apply : ∀[ (P ─✴ Q) ✴ P ⇒ Q ]
    apply (px ×⟨ sep ⟩ qx) =  px qx sep

  module _ {p q r} {P : SPred p} {Q : SPred q} {R : SPred r} where

    -- ✴-curry : ∀[ P ─✴ (Q ─✴ R) ] → ∀[ (P ✴ Q) ─✴ R ]
    -- ✴-curry f = wand (λ where
    --   (px ×⟨ sep₁ ⟩ qx) sep →
    --     let
    --       Φ , σ , σ' = ⊎-assoc (⊎-comm sep₁) {!⊎-comm sep!} 
    --       g = apply (f ×⟨ σ ⟩ px)
    --     in apply (g ×⟨ ⊎-comm σ' ⟩ qx))

    wand : ∀[ P ✴ Q ⇒ R ] → ∀[ P ⇒ Q ─✴ R ]
    wand f px qx s = f (px ×⟨ s ⟩ qx)

    com : ∀[ (P ─✴ Q) ✴ (Q ─✴ R) ⇒ (P ─✴ R) ]
    com (f ×⟨ s ⟩ g) px s' =
      let _ , eq₁ , eq₂ = ⊎-assoc (⊎-comm s) s' in
      g (f px eq₁) eq₂ 

    ✴-uncurry : ∀[ P ✴ Q ─✴ R ] → ∀[ P ─✴ (Q ─✴ R) ]
    ✴-uncurry f =
      λ px sep →
        λ qx sep' →
          let Φ , σ , σ' = ⊎-assoc sep sep'
          in  apply (f  ×⟨ σ' ⟩ (px ×⟨ σ ⟩ qx))

  -- | The update modality is a strong monad
  module Update where

    ⤇-map : ∀ {p q} {P : SPred p} {Q : SPred q} →
            ∀[ P ⇒ Q ] → ∀[ (⤇ P) ⇒ (⤇ Q) ]
    ⤇-map f mp σ with mp σ
    ... | _ , _ , σ' , p = -, -, σ' , f p

    ⤇-return : ∀ {p} {P : SPred p} → ∀[ P ⇒ ⤇ P ]
    ⤇-return px σ = -, -, σ , px

    ⤇-join : ∀ {p} {P : SPred p} → ∀[ ⤇ (⤇ P) ⇒ ⤇ P ]
    ⤇-join mmp σ with mmp σ
    ... | _ , _ , σ' , mp = mp σ'

    ⤇-bind : ∀ {q p} {P : SPred p} {Q : SPred q} →
             ∀[ P ⇒ ⤇ Q ] → ∀[ (⤇ P) ⇒ (⤇ Q) ]
    ⤇-bind f = ⤇-join ∘ ⤇-map f

    -- ⤇-& : ∀ {q} {Q : SPred q} → ∀[ P ✴ ⤇ Q ⇒ ⤇ (P ✴ Q) ]
    -- ⤇-& (p ×⟨ σ ⟩ mq) σ' = ?

  module _ where
    ≤-trans : Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁⊎τ₁=Φ₂) (τ₂ , Φ₂⊎τ₂=Φ₃) =
      let τ₃ , p , q = ⊎-assoc Φ₁⊎τ₁=Φ₂ Φ₂⊎τ₂=Φ₃ in τ₃ , q

record RawUnitalSep {c} (C : Set c) : Set (suc c) where
  field
    ε   : C
    sep : RawSep C

  open RawSep sep

  ε[_] : ∀ {ℓ} → Pred C ℓ → Set ℓ
  ε[ P ] = P ε

  {- Exactness -}
  module _ where

    Exactly : C → SPred c
    Exactly = flip _≡_

    _◆_ : C → C → SPred c
    Φₗ ◆ Φᵣ = Exactly Φₗ ✴ Exactly Φᵣ

  {- Emptyness -}
  module _ where

    Emp : SPred c
    Emp = Exactly ε

  {- Big seperating conjunction over an SPred -}
  module _ where

    data Bigstar {ℓ} (P : SPred ℓ) : SPred (ℓ ⊔ c) where
      emp  : ∀[ Emp ⇒ Bigstar P ]
      cons : ∀[ P ✴ Bigstar P ⇒ Bigstar P ]

  module _ {i ℓ} {I : Set i} where
    open import Data.List
    data Allstar (P : I → SPred ℓ) : List I → SPred (ℓ ⊔ c ⊔ i) where
      nil  :            ∀[ Emp ⇒ Allstar P [] ]
      cons : ∀ {x xs} → ∀[ P x ✴ Allstar P xs ⇒ Allstar P (x ∷ xs) ]

    -- not typed well..
    infixr 5 _:⟨_⟩:_
    pattern _:⟨_⟩:_ x p xs = cons (x ×⟨ p ⟩ xs)

record IsUnitalSep {c e} {C : Set c} (_≈_ : Rel C e) : Set (suc c ⊔ e) where
  field
    unital : RawUnitalSep C

  open RawUnitalSep unital

  field
    isSep  : IsSep sep

  open RawSep sep

  field
    ⊎-identityˡ    : ∀ {Φ} → ∀[ (Φ ≡_) ⇒ (ε ⊎ Φ) ]
    ⊎-identity⁻ˡ   : ∀ {Φ} → ∀[ (ε ⊎ Φ) ⇒ (Φ ≡_) ]
    ε-separateˡ    : ∀ {Φᵣ} → ∀[ (_⊎ Φᵣ ≣ ε) ⇒ (_≡ ε) ]

  open IsSep isSep

  ⊎-identityʳ : ∀ {Φ} → ∀[ (Φ ≡_) ⇒ (Φ ⊎ ε) ]
  ⊎-identityʳ = ⊎-comm ∘ ⊎-identityˡ

  ⊎-identity⁻ʳ : ∀ {Φ} → ∀[ (Φ ⊎ ε) ⇒ (Φ ≡_) ]
  ⊎-identity⁻ʳ = ⊎-identity⁻ˡ ∘ ⊎-comm

  ε-separateʳ : ∀ {Φₗ} → ∀[ (Φₗ ⊎_≣ ε) ⇒ (_≡ ε) ]
  ε-separateʳ = ε-separateˡ ∘ ⊎-comm

  module _ where
    ε⊎ε : ∀[ ε ⊎ ε ⇒ Emp ]
    ε⊎ε p with ⊎-identity⁻ˡ p
    ... | P.refl = P.refl

    ⋆-identityʳ : ∀ {P : SPred 0ℓ} → ∀[ P ⇒ P ✴ Emp ]
    ⋆-identityʳ px = px ×⟨ ⊎-identityʳ P.refl ⟩ P.refl

  module _ {p q} {P : SPred p} {Q : SPred q} where
    open Diamond

    ◇-ε : ∀[ P ◇ ε ⇒ P ]
    ◇-ε ⟪ px , σ ⟫ rewrite ⊎-identity⁻ˡ σ = px

    -- {-# BUILTIN REWRITE _≡_ #-}
    -- {-# REWRITE ◇-ε #-}

    -- _,,_ : ε[ P ◇─ Q ◇─ P ✴ Q ]
    -- _,,_ px qx = {!!}

  module _ {i ℓ} {I : Set i} {P : I → SPred ℓ} where
    open import Data.List
    singleton : ∀ {x} → ∀[ P x ⇒ Allstar P [ x ] ]
    singleton v = cons (v ×⟨ ⊎-identityʳ P.refl ⟩ (nil P.refl))

  {- A free preorder -}
  module _ where

    ≤-reflexive : Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive p = ε , ⊎-identityʳ p

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

    ε-minimal : ∀ {Φ} → ε ≤ Φ
    ε-minimal {Φ} = Φ , ⊎-identityˡ P.refl

  {- Framing where we forget the actual resource owned -}
  module ↑-Frames where

    infixl 1000 _↑
    _↑ : ∀ {ℓ} → SPred ℓ → SPred _
    P ↑ = P ✴ U

    pattern _⇑_ p sep = p ×⟨ sep ⟩ tt

    module _ {ℓ} {P : SPred ℓ} where

      return : ∀[ P ⇒ P ↑ ]
      return p = p ×⟨ ⊎-identityʳ P.refl ⟩ tt

      join : ∀[ (P ↑) ↑ ⇒ P ↑ ]
      join ((p ×⟨ σ₁ ⟩ tt) ×⟨ σ₂ ⟩ tt) = 
        let _ , σ₃ = ≤-trans (-, σ₁) (-, σ₂) in p ×⟨ σ₃ ⟩ tt

    module _ {ℓ₁ ℓ₂} {P : SPred ℓ₁} {Q : SPred ℓ₂} where

      map : ∀[ P ⇒ Q ] → ∀[ P ↑ ⇒ Q ↑ ]
      map f (px ⇑ sep) = f px ⇑ sep

    module _ {ℓ₁ ℓ₂} {P : SPred ℓ₁} {Q : SPred ℓ₂} where

      ↑-bind : ∀[ P ⇒ Q ↑ ] → ∀[ P ↑ ⇒ Q ↑ ]
      ↑-bind f px = join (map f px)

    {- Projections out of separating conjunction using framing -}
    module _ where

      π₁ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ (P ✴ Q) ⇒ P ↑ ]
      π₁ (px ×⟨ sep ⟩ _) = px ⇑ sep

      π₂ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ (P ✴ Q) ⇒ Q ↑ ]
      π₂ (_ ×⟨ sep ⟩ qx) = qx ⇑ ⊎-comm sep

  -- module ▣-Frames {ℓ} where

  --   frame_out_ : C → SPred ℓ → SPred (c ⊔ ℓ)
  --   frame Φ out P = (Exactly Φ) ✴ P

  --   _◇_ : SPred ℓ → C → SPred (c ⊔ ℓ)
  --   _◇_ = flip frame_out_

  --   _⇒′_ : ∀ {A ℓ₁ ℓ₂} → (P : Pred A ℓ₁) → (∀ {a} → P a → Pred A ℓ₂) → Pred A _
  --   P ⇒′ Q = λ x → (p : x ∈ P) → x ∈ Q p

  --   π₁ : ∀ {P Q : SPred ℓ} → ∀[ (P ✴ Q) ⇒′ (P ◇_ ∘ Conj.Φᵣ) ]
  --   π₁ (px ×⟨ σ ⟩ qx) = P.refl ×⟨ ⊎-comm σ ⟩ px

  --   π₂ : ∀ {P Q : SPred ℓ} → ∀[ (P ✴ Q) ⇒′ (Q ◇_ ∘ Conj.Φₗ) ]
  --   π₂ (px ×⟨ σ ⟩ qx) = P.refl ×⟨ σ ⟩ qx

    -- _─⟨_⟩_ : (P : SPred ℓ₁) → Carrier → (Q : SPred ℓ₂)  → SPred _
    -- P ─⟨ j ⟩ Q = P ⇒ Q ▣ j 


record IsConcattative {c} {C : Set c} (sep : RawSep C) (_∙_ : C → C → C) : Set c where
  open RawSep sep

  field
    ⊎-∙ : ∀ {Φₗ Φᵣ} → Φₗ ⊎ Φᵣ ≣ (Φₗ ∙ Φᵣ)

record Separation ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  field
    raw          : RawSep Carrier
    isSep : IsSep raw

  open RawSep raw
  open IsSep isSep public

record UnitalSep ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  field
    isUnitalSep : IsUnitalSep _≈_

  open IsUnitalSep isUnitalSep public

record MonoidalSep ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set public 

  field
    _∙_         : Carrier → Carrier → Carrier
    isUnitalSep : IsUnitalSep _≈_

  open IsUnitalSep isUnitalSep
  open RawUnitalSep unital
  open RawSep sep

  field
    isConcat    : IsConcattative sep _∙_

  open IsConcattative isConcat public

  -- module _ {ℓ₁ ℓ₂} where
  --   _─✫_ : (P : SPred ℓ₁) (Q : SPred ℓ₂)  → SPred _
  --   P ─✫ Q = λ Φ₁ → ∀ {Φ₂} → P Φ₂ → Q (Φ₁ ∙ Φ₂)

  --   ✫─✴ : ∀ {P Q} → ∀[ (P ─✴ Q) ⇒ (P ─✫ Q) ]
  --   ✫─✴ f = λ px → f px ⊎-∙

  {- Disjoint extension -}
  -- module _ {ℓ₁ ℓ₂} where

    -- infixr 8 _─◆′_
    -- _─◆′_ : (P : SPred ℓ₁) (Q : ∀ {i} → P i → SPred ℓ₂)  → SPred _
    -- P ─◆′ Q = λ i → (p : P i) → ∃ (Q p)

    -- infixr 8 _─◆_
    -- _─◆_ : (P : SPred ℓ₁) (Q : SPred ℓ₂)  → SPred _
    -- P ─◆ Q = P ─◆′ (const Q)

  -- {- Framing is functorial -}
  -- module _ where

  --   ▣-map : ∀ {j} {P : SPred ℓ₁} {Q : SPred ℓ₂} → ∀[ P ─◆ Q ] → ∀[ P ▣ j ─◆ Q ▣ j ]
  --   ▣-map f (px ×⟨ ◆ ⟩ qx) with f qx
  --   ... | ext , rx = -, px ×⟨ ⊎-∙ ⟩ rx
