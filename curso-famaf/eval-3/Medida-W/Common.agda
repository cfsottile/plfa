module Common where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s≤s; _≤?_; _≟_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  9 S_

data Type : Set where
  τ : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

length : Context → ℕ
length ∅  =  zero
length (Γ , _) =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {_ , A} {zero} (s≤s p) = A
lookup {_ , _} {suc n} (s≤s p) = lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s p) = Z
count {_ , x} {suc n} (s≤s p) = S (count p)

ext : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -------------------------------
  → ∀ {A B} → Γ , B ∋ A → Δ , B ∋ A
ext ρ Z = Z
ext ρ (S n) = S ρ n
