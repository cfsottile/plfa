module Lambda where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s≤s; _≤?_; _≟_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common

infix  4 _⊢ᵦ_

infix  5 ƛᵦ_
infixl 7 _·ᵦ_
infix  9 `ᵦ_
infix  9 #ᵦ_

data _⊢ᵦ_ : Context → Type → Set where

  `ᵦ_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ᵦ A

  ƛᵦ_ : ∀ {Γ A B}
    → Γ , A ⊢ᵦ B
      ---------
    → Γ ⊢ᵦ A ⇒ B

  _·ᵦ_ : ∀ {Γ A B}
    →  Γ ⊢ᵦ A ⇒ B   →    Γ ⊢ᵦ A
       ----------------------
    →        Γ ⊢ᵦ B

#ᵦ_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ᵦ lookup (toWitness n∈Γ)
#ᵦ_ n {n∈Γ} = `ᵦ count (toWitness n∈Γ)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → ∀ {A} → Γ ⊢ᵦ A → Δ ⊢ᵦ A
rename ρ (`ᵦ n) = `ᵦ ρ n
rename ρ (ƛᵦ t) = ƛᵦ rename (ext ρ) t
rename ρ (t ·ᵦ s) = (rename ρ t) ·ᵦ (rename ρ s)

exts : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ᵦ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ᵦ A)
exts σ Z = `ᵦ Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A}  →  Γ ∋ A  →  Δ ⊢ᵦ A)
    -----------------------
  → ∀ {A}   →  Γ ⊢ᵦ A  →  Δ ⊢ᵦ A
subst σ (`ᵦ n) = σ n
subst σ (ƛᵦ t) = ƛᵦ subst (exts σ) t
subst σ (t ·ᵦ s) = (subst σ t) ·ᵦ (subst σ s)

_[_]ᵦ : ∀ {Γ A B}
  → Γ , B ⊢ᵦ A
  → Γ ⊢ᵦ B
    ---------
  → Γ ⊢ᵦ A
_[_]ᵦ {Γ} {A} {B} t s = subst σ t
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ᵦ A
  σ Z = s
  σ (S x) = `ᵦ x

data Valueᵦ : ∀ {Γ A} → Γ ⊢ᵦ A → Set where
  V-x : ∀ {Γ A} {x : Γ ∋ A} → Valueᵦ (`ᵦ x)
  V-ƛᵦ : ∀ {Γ A B} {M : Γ , A ⊢ᵦ B} → Valueᵦ (ƛᵦ M)

infix 2 _⟶ᵦ_

data _⟶ᵦ_ : ∀ {Γ A} → (Γ ⊢ᵦ A) → (Γ ⊢ᵦ A) → Set where

  β-ƛᵦ : ∀ {Γ A B} {t : Γ , A ⊢ᵦ B} {s : Γ ⊢ᵦ A}
      --------------------------
    → (ƛᵦ t) ·ᵦ s ⟶ᵦ t [ s ]ᵦ

  ξ-ƛᵦ : ∀ {Γ A B} {t t' : Γ , A ⊢ᵦ B}
    →   t ⟶ᵦ t'
      -----------
    → ƛᵦ t ⟶ᵦ ƛᵦ t'

  ξ-·₁ : ∀ {Γ A B} {t t' : Γ ⊢ᵦ A ⇒ B} {s : Γ ⊢ᵦ A}
    →     t ⟶ᵦ t'
      ---------------
    → t ·ᵦ s ⟶ᵦ t' ·ᵦ s

  ξ-·₂ : ∀ {Γ A B} {t : Γ ⊢ᵦ A ⇒ B} {s s' : Γ ⊢ᵦ A}
    →     s ⟶ᵦ s'
      ---------------
    → t ·ᵦ s ⟶ᵦ t ·ᵦ s'

infix  2 _⟶ᵦⁿ_
infix  1 begin_
infixr 2 _⟶ᵦ⟨_⟩_
infix  3 _∎

data _⟶ᵦⁿ_ {Γ A} : (Γ ⊢ᵦ A) → (Γ ⊢ᵦ A) → Set where

  _∎ : (t : Γ ⊢ᵦ A)
      ------
    → t ⟶ᵦⁿ t

  step⟶ᵦ : (t : Γ ⊢ᵦ A) {s r : Γ ⊢ᵦ A}
    → s ⟶ᵦⁿ r
    → t ⟶ᵦ s
      ------
    → t ⟶ᵦⁿ r

pattern _⟶ᵦ⟨_⟩_ t t⟶ᵦs s⟶ᵦⁿr = step⟶ᵦ t s⟶ᵦⁿr t⟶ᵦs

begin_ : ∀ {Γ A} {t s : Γ ⊢ᵦ A}
  → t ⟶ᵦⁿ s
    ------
  → t ⟶ᵦⁿ s
begin t⟶ᵦⁿs = t⟶ᵦⁿs

postulate
  confluenceᵦ : ∀ {Γ A} {t s r u : Γ ⊢ᵦ A}
    → ((t ⟶ᵦⁿ s) × (t ⟶ᵦⁿ r))
      ---------------------
    → ∃[ u ] ((s ⟶ᵦⁿ u) × (r ⟶ᵦⁿ u))
