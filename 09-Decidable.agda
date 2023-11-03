import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

data Bool : Set where
  true : Bool
  false : Bool

T : Bool → Set
T true = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) zero ()
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (n m : ℕ) → Dec (n ≤ m)
zero ≤? m = yes z≤n
suc n ≤? zero = no ¬s≤z
suc n ≤? suc m with n ≤? m
... | yes n≤m = yes (s≤s n≤m)
... | no ¬n≤m = no (¬s≤s ¬n≤m)

_<?_ : ∀ (n m : ℕ) → Dec (n < m)
zero <? zero = no λ ()
zero <? suc m = yes z<s
suc n <? zero = no λ ()
suc n <? suc m with n <? m
... | yes n<m = yes (s<s n<m)
... | no ¬n<m = no λ{ (s<s n<m) → ¬n<m n<m }

-- ≡-suc : ∀ (n m : ℕ) → suc n ≡ suc m → n ≡ m
-- ≡-suc zero zero sn≡sm = refl
-- ≡-suc (suc n) (suc m) refl = refl

_≡ℕ?_ : ∀ (n m : ℕ) → Dec (n ≡ m)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc m = no λ ()
suc n ≡ℕ? zero = no λ ()
suc n ≡ℕ? suc m with n ≡ℕ? m
... | yes n≡m = yes (Eq.cong suc n≡m)
-- Claro, una vez que probaste que son iguales, SON LO MISMO
... | no  n≢m = no λ{ refl → n≢m refl }

infix 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
yes a →-dec yes b = yes λ _ → b
-- _  →-dec yes b = yes λ _ → b
yes a →-dec no ¬b = no λ a→b → ¬b (a→b a)
no ¬a →-dec _     = yes λ a → ⊥-elim (¬a a)

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

-- TODO ejercicios erasure

-- False : ∀ {Q} → Dec Q → Set
-- False (yes q) = ⊥
-- False (no ¬q) = ⊤

-- toWitnessFalse : ∀ {A : Set} {D : Dec A} → False D → ¬ A
-- toWitnessFalse {A} {no ¬a} f = ¬a

-- fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → False D
-- fromWitnessFalse {A} {yes a} ¬a = ¬a a
-- fromWitnessFalse {A} {no ¬a} ¬a' = tt

F : Bool → Set
F true = ⊥
F false = ⊤

False : ∀ {Q} → Dec Q → Set
False Q = F ⌊ Q ⌋

toWitnessFalse : ∀ {A : Set} {D : Dec A} → F ⌊ D ⌋ → ¬ A
toWitnessFalse {A} {yes _} ()
toWitnessFalse {A} {no ¬a} tt = ¬a

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → F ⌊ D ⌋
fromWitnessFalse {A} {yes a} ¬a = ¬a a
fromWitnessFalse {A} {no ¬a} _  = tt

-- T ⌊ A ⌋ está habitado cuando A está habitado
-- F ⌊ A ⌋ está habitado cuando ¬ A está habitado
