{-# OPTIONS --without-K #-}

-- A separation algebra.
-- Axiomatization based on
-- "A fresh look at Separation Algebras and Share Accounting" (Dockins et al)
module Relation.Unary.Separation where

open import Function
open import Level

open import Data.Unit using (tt; ⊤)
open import Data.Product hiding (map)
open import Data.List.Relation.Ternary.Interleaving.Propositional hiding (map)
open import Data.List.Relation.Binary.Equality.Propositional

open import Relation.Unary hiding (Empty)
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
  Φ₁ ≤ Φ = ∃ λ Φ₂ → Φ₁ ⊎ Φ₂ ≣ Φ

  -- remainder
  rem : ∀ {x y} → x ≤ y → Carrier
  rem (z , _) = z

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
  P ─✴ Q = λ Φᵢ → ∀ {Φₚ Φ} → P Φₚ → Φᵢ ⊎ Φₚ ≣ Φ → Q Φ

  -- | The update modality

  ⤇ : ∀ {p} → SPred p → SPred (a ⊔ p)
  ⤇ P Φᵢ = ∀ {Φⱼ Φₖ} → Φᵢ ⊎ Φⱼ ≣ Φₖ → ∃₂ λ Φₗ Φ → Φₗ ⊎ Φⱼ ≣ Φ × P Φₗ
    -- Φᵢ is what we own, Φⱼ is an arbitrary frame.
    -- We may update Φᵢ as long as we do not disturb the framing

  infixr 8 _==✴_
  _==✴_ : ∀ {p q} → (P : SPred p) (Q : SPred q) → SPred (p ⊔ q ⊔ a)
  P ==✴ Q = P ─✴ (⤇ Q)

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

record IsSep {ℓ₁} {A} (s : RawSep {ℓ₁} A) : Set ℓ₁ where
  open RawSep s

  field
    -- ⊎-functional   : ∀ {Φ₁ Φ₂ Φ Φ'}   → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ⊎ Φ₂ ≣ Φ' → Φ ≈ Φ'
    -- ⊎-cancellative : ∀ {Φ₁ Φ₁' Φ₂}    → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₁' ⊎ Φ₂ ⇒ (λ _ → Φ₁ ≈ Φ₁') ]
    -- we axiomatize the basic laws for splittings
    ⊎-comm  : ∀ {Φ₁ Φ₂}        → ∀[ Φ₁ ⊎ Φ₂ ⇒ Φ₂ ⊎ Φ₁ ]
    ⊎-assoc : ∀ {a b ab c abc} → a ⊎ b ≣ ab → ab ⊎ c ≣ abc →
                                 ∃ λ bc → a ⊎ bc ≣ abc × b ⊎ c ≣ bc

  ⊎-unassoc : ∀ {b c bc a abc} → a ⊎ bc ≣ abc → b ⊎ c ≣ bc →
                                 ∃ λ ab → a ⊎ b ≣ ab × ab ⊎ c ≣ abc
  ⊎-unassoc σ₁ σ₂ =
    let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₁)
    in -, ⊎-comm σ₄ , ⊎-comm σ₃
                                
  variable
    Φ₁ Φ₂ Φ₃ Φ : A

  module _ where
    resplit : ∀ {a b c d ab cd abcd} →
              a ⊎ b ≣ ab → c ⊎ d ≣ cd → ab ⊎ cd ≣ abcd →
              ∃₂ λ ac bd → a ⊎ c ≣ ac × b ⊎ d ≣ bd × ac  ⊎ bd  ≣ abcd
    resplit σ₁ σ₂ σ     with ⊎-assoc σ₁ σ
    ... | bcd , σ₃ , σ₄ with ⊎-unassoc σ₄ (⊎-comm σ₂)
    ... | bd  , σ₅ , σ₆ with ⊎-unassoc σ₃ σ₆
    ... | abd , σ₇ , σ₈ with ⊎-unassoc (⊎-comm σ₈) σ₇
    ... | ac  , τ  , τ' = -, -, ⊎-comm τ , σ₅ , τ'

  -- pairs commute
  module _ {p q} {P : SPred p} {Q : SPred q} where
    ✴-swap : ∀[ (P ✴ Q) ⇒ (Q ✴ P) ]
    ✴-swap (px ×⟨ σ ⟩ qx) = qx ×⟨ ⊎-comm σ ⟩ px

  -- pairs rotate and reassociate
  module _ {p q r} {P : SPred p} {Q : SPred q} {R : SPred r} where
    ✴-assocₗ : ∀[ P ✴ (Q ✴ R) ⇒ (P ✴ Q) ✴ R ]
    ✴-assocₗ (p ×⟨ σ₁ ⟩ (q ×⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₁) in
      (p ×⟨ ⊎-comm σ₄ ⟩ q) ×⟨ ⊎-comm σ₃ ⟩ r

    ✴-assocᵣ : ∀[ (P ✴ Q) ✴ R ⇒ P ✴ (Q ✴ R) ]
    ✴-assocᵣ ((p ×⟨ σ₁ ⟩ q) ×⟨ σ₂ ⟩ r) =
      let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in
      p ×⟨ σ₃ ⟩ q ×⟨ σ₄ ⟩ r

    ✴-rotateᵣ : ∀[ P ✴ (Q ✴ R) ⇒ R ✴ P ✴ Q ]
    ✴-rotateᵣ (p ×⟨ σ₁ ⟩ (q ×⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₁) in
      r ×⟨ σ₃ ⟩ p ×⟨ ⊎-comm σ₄ ⟩ q

    ✴-rotateₗ : ∀[ P ✴ (Q ✴ R) ⇒ Q ✴ R ✴ P ]
    ✴-rotateₗ (p ×⟨ σ₁ ⟩ (q ×⟨ σ₂ ⟩ r)) =
      let _ , σ₃ , σ₄ = ⊎-assoc σ₂ (⊎-comm σ₁) in
      q ×⟨ σ₃ ⟩ r ×⟨ σ₄ ⟩ p

  module _ {p q} {P : SPred p} {Q : SPred q} where
    apply : ∀[ (P ─✴ Q) ✴ P ⇒ Q ]
    apply (px ×⟨ sep ⟩ qx) =  px qx sep

  -- mapping
  module _ {p q p' q'}
    {P : SPred p} {Q : SPred q} {P' : SPred p'} {Q' : SPred q'} where

    ⟨_⟨✴⟩_⟩ : ∀[ P ⇒ P' ] → ∀[ Q ⇒ Q' ] → ∀[ P ✴ Q ⇒ P' ✴ Q' ]
    ⟨_⟨✴⟩_⟩ f g (px ×⟨ sep ⟩ qx) = (f px) ×⟨ sep ⟩ (g qx)

    both : ∀[ (P ─✴ P') ✴ (Q ─✴ Q') ⇒ P ✴ Q ─✴ P' ✴ Q' ]
    both (f ×⟨ σ₁ ⟩ g) (px ×⟨ σ₂ ⟩ qx) σ₃ with resplit σ₁ σ₂ σ₃
    ... | _ , _ , σ₄ , σ₅ , σ₆ = apply (f ×⟨ σ₄ ⟩ px) ×⟨ σ₆ ⟩ apply (g ×⟨ σ₅ ⟩ qx)

  module _ {p q r} {P : SPred p} {Q : SPred q} {R : SPred r} where

    ✴-curry : ∀[ (P ─✴ (Q ─✴ R)) ⇒ (P ✴ Q) ─✴ R ]
    ✴-curry f (p ×⟨ σ₁ ⟩ q) σ₂ =
      let _ , σ₃ , σ₄ = ⊎-unassoc σ₂ σ₁ in f p σ₃ q σ₄

    wand : ∀[ (P ✴ Q) ⇒ R ] → ∀[ P ⇒ (Q ─✴ R) ]
    wand f px qx s = f (px ×⟨ s ⟩ qx)

    com : ∀[ (P ─✴ Q) ✴ (Q ─✴ R) ⇒ (P ─✴ R) ]
    com (f ×⟨ s ⟩ g) px s' = let _ , eq₁ , eq₂ = ⊎-assoc (⊎-comm s) s' in g (f px eq₂) eq₁

    ✴-uncurry : ∀[ (P ✴ Q ─✴ R) ⇒ P ─✴ (Q ─✴ R) ]
    ✴-uncurry f p σ₁ q σ₂ = let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in f (p ×⟨ σ₄ ⟩ q) σ₃

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

    -- strength
    &-⤇ : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ P ✴ ⤇ Q ⇒ ⤇ (P ✴ Q) ]
    &-⤇ (p ×⟨ σ ⟩ mq) σ' with ⊎-assoc (⊎-comm σ) σ'
    ... | _ , σ₂ , σ₃ with mq σ₂
    ... | _ , _ , σ₄ , q with ⊎-assoc (⊎-comm σ₃) (⊎-comm σ₄)
    ... | _ , σ₅ , σ₆ = -, -, ⊎-comm σ₅ , (p ×⟨ σ₆ ⟩ q)

    -- reverse strength
    ⤇-& : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ ⤇ P ✴ Q ⇒ ⤇ (P ✴ Q) ]
    ⤇-& = ⤇-map ✴-swap ∘ &-⤇ ∘ ✴-swap

  module _ where
    postulate ≤-⊎ : ∀ {Φ₁ Φ₂ Φ Φ'} → Φ₁ ⊎ Φ₂ ≣ Φ → Φ₁ ≤ Φ' → Φ₂ ≤ Φ' → Φ ≤ Φ'

    ≤-trans : Φ₁ ≤ Φ₂ → Φ₂ ≤ Φ₃ → Φ₁ ≤ Φ₃
    ≤-trans (τ₁ , Φ₁⊎τ₁=Φ₂) (τ₂ , Φ₂⊎τ₂=Φ₃) =
      let τ₃ , p , q = ⊎-assoc Φ₁⊎τ₁=Φ₂ Φ₂⊎τ₂=Φ₃ in τ₃ , p

record IsUnitalSep {c} {C : Set c} (sep : RawSep C) : Set (suc c) where
  field
    overlap {{ isSep }}  : IsSep sep

  open RawSep sep

  field
    ε              : C
    ⊎-idˡ    : ∀ {Φ} →  ε ⊎ Φ ≣ Φ
    ⊎-id⁻ˡ   : ∀ {Φ} → ∀[ (ε ⊎ Φ) ⇒ (Φ ≡_) ]

  open IsSep isSep

  ⊎-idʳ : ∀ {Φ} → Φ ⊎ ε ≣ Φ
  ⊎-idʳ = ⊎-comm ⊎-idˡ

  ⊎-id⁻ʳ : ∀ {Φ} → ∀[ (Φ ⊎ ε) ⇒ (Φ ≡_) ]
  ⊎-id⁻ʳ = ⊎-id⁻ˡ ∘ ⊎-comm

  infix 10 ε[_]
  ε[_] : ∀ {ℓ} → Pred C ℓ → Set ℓ
  ε[ P ] = P ε

  {- Exactness -}
  module _ where

    Exactly : C → SPred c
    Exactly = flip _≡_

    -- disjointness
    _◆_ : C → C → SPred c
    Φₗ ◆ Φᵣ = Exactly Φₗ ✴ Exactly Φᵣ

  {- Emptyness -}
  module _ where
  
    data Empty {p} (P : Set p) : SPred (c ⊔ p) where
      emp : P → Empty P ε
      
    pattern empty = emp tt

    Emp : SPred c
    Emp = Empty ⊤

    -- Arr : ∀ {a p} → Set a → SPred p → SPred (c ⊔ a ⊔ p)
    -- Arr A P = λ Φ → ∀ {e} → Empty A e → P Φ

    -- pure : ∀ {a p} {A : Set a} {P : SPred p} → ε[ P ─✴ Arr A P ]
    -- pure px σ (emp a) rewrite ⊎-id⁻ˡ σ = px

    -- app : ∀ {a p q} {A : Set a} {P : SPred p} {Q : SPred q} → ∀[ Arr A (P ─✴ Q) ⇒ Arr A P ⇒ Arr A Q ]
    -- app f p (emp a) = {!!}

  {- Big seperating conjunction over an SPred -}
  module _ where

    data Bigstar {ℓ} (P : SPred ℓ) : SPred (ℓ ⊔ c) where
      emp  : ε[ Bigstar P ]
      cons : ∀[ P ✴ Bigstar P ⇒ Bigstar P ]

  module _ {i ℓ} {I : Set i} where
    open import Data.List
    data Allstar (P : I → SPred ℓ) : List I → SPred (ℓ ⊔ c ⊔ i) where
      nil  :            ε[ Allstar P [] ]
      cons : ∀ {x xs} → ∀[ P x ✴ Allstar P xs ⇒ Allstar P (x ∷ xs) ]

    -- not typed well..
    infixr 5 _:⟨_⟩:_
    pattern _:⟨_⟩:_ x p xs = cons (x ×⟨ p ⟩ xs)

  module _ where
    ε⊎ε : ∀[ ε ⊎ ε ⇒ Emp ]
    ε⊎ε p with ⊎-id⁻ˡ p
    ... | (P.refl) = empty

    ⋆-idʳ : ∀ {p} {P : SPred p} → ∀[ P ⇒ P ✴ Emp ]
    ⋆-idʳ px = px ×⟨ ⊎-idʳ ⟩ empty

    -- a resource-polymorphic function is a pure wand
    wandit : ∀ {p q} {P : SPred p} {Q : SPred q} → ∀[ P ⇒ Q ] → ε[ P ─✴ Q ]
    wandit f p σ rewrite ⊎-id⁻ˡ σ = f p

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

  ─[id] : ∀ {p} {P : Pred _ p} → ε[ P ─✴ P ]
  ─[id] px σ rewrite ⊎-id⁻ˡ σ = px

  -- internal versions of the strong monadic structure on update
  module _ where

    ⤇-return : ∀ {p} {P : SPred p} → ε[ P ─✴ (⤇ P) ]
    ⤇-return px σ fr with ⊎-id⁻ˡ σ
    ... | P.refl = -, -, fr , px

    ⤇-bind : ∀ {p q}{P : SPred p}{Q : SPred q} → ε[ (P ─✴ ⤇ Q) ─✴ ((⤇ P) ─✴ ⤇ Q) ]
    ⤇-bind f σf p σₚ fr with ⊎-id⁻ˡ σf
    ... | P.refl with ⊎-assoc (⊎-comm σₚ) fr
    ... | _ , σ₁ , σ₂ with p σ₁
    ... | Δ , Σ , σ₃ , px with ⊎-assoc (⊎-comm σ₂) (⊎-comm σ₃)
    ... | _ , σ₄ , σ₅ = f px σ₅ (⊎-comm σ₄)

    postulate &-⤇ : ∀ {p q} {P : SPred p} {Q : SPred q} → ε[ P ✴ ⤇ Q ─✴ ⤇ (P ✴ Q) ]

  module _ {p q} {P : SPred p} {Q : SPred q} where
    pair : ε[ P ◇─ (Q ◇─ P ✴ Q) ]
    pair ⟪ px , σ₁ ⟫ ⟪ qx , σ₂ ⟫ rewrite ⊎-id⁻ˡ σ₁ = px ×⟨ σ₂ ⟩ qx

  module _ {p} {P : SPred p} where
    ◇-ε : ∀[ P ◇ ε ⇒ P ]
    ◇-ε ⟪ px , σ ⟫ rewrite ⊎-id⁻ˡ σ = px

  module _ {i ℓ} {I : Set i} {P : I → SPred ℓ} where
    open import Data.List
    singleton : ∀ {x} → ∀[ P x ⇒ Allstar P [ x ] ]
    singleton v = cons (v ×⟨ ⊎-idʳ ⟩ nil)

  {- A free preorder -}
  module _ where

    ≤-reflexive : Φ₁ ≡ Φ₂ → Φ₁ ≤ Φ₂
    ≤-reflexive P.refl = ε , ⊎-idʳ

    ≤-isPreorder : IsPreorder _≡_ _≤_
    ≤-isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive = ≤-reflexive
      ; trans = ≤-trans }

    ≤-preorder : Preorder _ _ _
    ≤-preorder = record { isPreorder = ≤-isPreorder }

    ε-minimal : ∀ {Φ} → ε ≤ Φ
    ε-minimal {Φ} = Φ , ⊎-idˡ

  {- Framing where we forget the actual resource owned -}
  module ↑-Frames where

    infixl 1000 _↑
    _↑ : ∀ {ℓ} → SPred ℓ → SPred _
    P ↑ = P ✴ U

    pattern _⇑_ p sep = p ×⟨ sep ⟩ tt

    module _ {ℓ} {P : SPred ℓ} where

      return : ∀[ P ⇒ P ↑ ]
      return p = p ×⟨ ⊎-idʳ ⟩ tt

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

record IsConcattative {c} {C : Set c} (sep : RawSep C) : Set (suc c) where
  open RawSep sep

  field
    _∙_ : C → C → C 
    ⊎-∙ : ∀ {Φₗ Φᵣ} → Φₗ ⊎ Φᵣ ≣ (Φₗ ∙ Φᵣ)

  postulate ≤-∙ : ∀ {Φₗ Φᵣ Φ} → Φₗ ≤ Φᵣ → (Φ ∙ Φₗ) ≤ (Φ ∙ Φᵣ)
  postulate ⊎-∙ₗ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ⊎ Φ₂ ≣ Φ → (Φₑ ∙ Φ₁) ⊎ Φ₂ ≣ (Φₑ ∙ Φ)

record Separation ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set

  field
    overlap {{ raw }}   : RawSep Carrier
    overlap {{ isSep }} : IsSep raw

record UnitalSep ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    set : Setoid ℓ₁ ℓ₂

  open Setoid set

  field
    overlap {{ sep }}         : RawSep Carrier
    overlap {{ isUnitalSep }} : IsUnitalSep sep

record MonoidalSep c : Set (suc c) where
  field
    Carrier : Set c
    overlap {{ sep }}         : RawSep Carrier
    overlap {{ isSep }}       : IsSep sep
    overlap {{ isUnitalSep }} : IsUnitalSep sep
    overlap {{ isConcat }}    : IsConcattative sep

open RawSep ⦃...⦄ public
open IsConcattative ⦃...⦄ public
open IsUnitalSep ⦃...⦄ public
open UnitalSep ⦃...⦄ public
open IsSep ⦃...⦄ public
open MonoidalSep ⦃...⦄ public hiding (Carrier)
