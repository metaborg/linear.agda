-- Loosely based on https://www.seas.upenn.edu/~cis552/11fa/lectures/concurrency.html

open import Data.Unit using (⊤; tt)
open import Data.List
open import Data.String as String
open import Data.Product
open import Agda.Primitive
open import Function

module Concurrent.Action where

data Action {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  bind : {A : Set a}
         (a : F A) (k : A → Action F) → Action F
  fork : (a b : Action F) → Action F
  done : Action F

C : ∀ {a b} (F : Set a → Set b) → Set a → Set _
C F A = (A → Action F) → Action F

-- because universe levels
record RawMonad {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  constructor mkRawMonad
  field
    _>>=_  : {A B : Set a}
             (m : M A) (f : A → M B) → M B
    return : {A : Set a} →
             A → M A

  _>>_ : {A B : Set a} →
         M A → M B → M B
  _>>_ m f = m >>= (λ _ → f)

C-Monad : {a b : Level} {F : Set a → Set b} → RawMonad (C F)
C-Monad =
  record {
    _>>=_ = λ m f k → m (λ a → f a k) ;
    return = λ a k → k a
  }

lift : {F : Set → Set} {A : Set} →
       F A → C F A
lift = bind

stop : {F : Set → Set} {A : Set} →
       C F A
stop k = done

par : {F : Set → Set} {A : Set}
      (c₁ c₂ : C F A) → C F A
par c₁ c₂ k = fork (c₁ k) (c₂ k)

action : {F : Set → Set} {A : Set} →
         C F A → Action F
action c = c (λ a → done)

fork′ : {F : Set → Set}
        (c : C F ⊤) → C F ⊤
fork′ c k = fork (action c) (k tt)

module _ {F : Set → Set} ⦃ M : RawMonad F ⦄ where

  open RawMonad M

  {-# TERMINATING #-} -- hmm
  sched : List (Action F) → F ⊤
  sched []                = return tt
  sched (bind fa k ∷ xs)  = fa >>= λ a → sched (xs ∷ʳ k a)
  sched (fork a₁ a₂ ∷ xs) = sched (xs ∷ʳ a₁ ∷ʳ a₂)
  sched (done ∷ xs)       = sched xs

  run : {A : Set} →
        C F A → F ⊤
  run c = sched [ action c ]

-- A test

IOish : Set → Set
IOish A = A × String

write : String → IOish ⊤
write s = tt , s

instance
  IOish-Monad : RawMonad IOish
  IOish-Monad =
    record {
      return = λ x → x , "" ;
      _>>=_  = λ where
        (a , s₁) f → case f a of λ where
          (b , s₂) → b , s₁ String.++ s₂ }

say-twice : String → C IOish ⊤
say-twice s = do
  lift $ write s
  lift $ write s
  where open RawMonad C-Monad

test-prog : C IOish ⊤
test-prog = do
  lift $ write "start "
  fork′ (say-twice "hello ")
  say-twice "world "
  lift $ write "end"
  where open RawMonad C-Monad

test-prog₁ : C IOish ⊤
test-prog₁ = do
  lift $ write "start "
  say-twice "hello "
  say-twice "world "
  lift $ write "end"
  where open RawMonad C-Monad

