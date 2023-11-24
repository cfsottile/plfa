module LambdaG where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; s≤s; _≤?_; _≟_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common

infix  4 _⊢_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    →  Γ ⊢ A ⇒ B   →    Γ ⊢ A
       ----------------------
    →        Γ ⊢ B

  _⟪_⟫ : ∀ {Γ A B}
    →  Γ ⊢ A  →  Γ ⊢ B
       ---------------
    →       Γ ⊢ A

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → ∀ {A} → Γ ⊢ A → Δ ⊢ A
rename ρ (` n) = ` ρ n
rename ρ (ƛ t) = ƛ rename (ext ρ) t
rename ρ (t · s) = (rename ρ t) · (rename ρ s)
rename ρ (t ⟪ s ⟫) = rename ρ t ⟪ rename ρ s ⟫

exts : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A}  →  Γ ∋ A  →  Δ ⊢ A)
    -----------------------
  → ∀ {A}   →  Γ ⊢ A  →  Δ ⊢ A
subst σ (` n) = σ n
subst σ (ƛ t) = ƛ subst (exts σ) t
subst σ (t · s) = (subst σ t) · (subst σ s)
subst σ (t ⟪ s ⟫) = subst σ t ⟪ subst σ s ⟫

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} t s = subst σ t
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z = s
  σ (S x) = ` x

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-x : ∀ {Γ A} {x : Γ ∋ A} → Value (` x)
  V-ƛ : ∀ {Γ A B} {M : Γ , A ⊢ B} → Value (ƛ M)

infix 2 _⟶_

data _⟶_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  β-ƛ : ∀ {Γ A B} {t : Γ , A ⊢ B} {s : Γ ⊢ A}
      --------------------------
    → (ƛ t) · s ⟶ t [ s ] ⟪ s ⟫

  -- β-ƛ : ∀ {Γ A B} {t : Γ , A ⊢ B} {s : Γ ⊢ C}
  --     -------------------------
  --   → (ƛ t) ⟪ s ⟫

  ξ-β : ∀ {Γ A B C} {t : Γ ⊢ A ⇒ B} {s : Γ ⊢ C} {r : Γ ⊢ A}
      ----------------------------
    → t ⟪ s ⟫ · r ⟶ (t · r) ⟪ s ⟫

  ξ-ƛ : ∀ {Γ A B} {t t' : Γ , A ⊢ B}
    →   t ⟶ t'
      -----------
    → ƛ t ⟶ ƛ t'

  ξ-·₁ : ∀ {Γ A B} {t t' : Γ ⊢ A ⇒ B} {s : Γ ⊢ A}
    →     t ⟶ t'
      ---------------
    → t · s ⟶ t' · s

  ξ-·₂ : ∀ {Γ A B} {t : Γ ⊢ A ⇒ B} {s s' : Γ ⊢ A}
    →     s ⟶ s'
      ---------------
    → t · s ⟶ t · s'

  ξ-bin₁ : ∀ {Γ A B} {t t' : Γ ⊢ A} {s : Γ ⊢ B}
    →    t ⟶ t'
      -------------------
    → t ⟪ s ⟫ ⟶ t' ⟪ s ⟫

  ξ-bin₂ : ∀ {Γ A B} {t : Γ ⊢ A} {s s' : Γ ⊢ B}
    →    s ⟶ s'
      -------------------
    → t ⟪ s ⟫ ⟶ t ⟪ s' ⟫

infix  2 _⟶ⁿ_
infix  1 begin_
-- infixr 2 _⟶⟨_⟩_
infix  3 _∎

data _⟶ⁿ_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M ⟶ⁿ M

  step⟶ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M ⟶ⁿ N
    → L ⟶ M
      ------
    → L ⟶ⁿ N

-- pattern _⟶⟨_⟩_ L L⟶M M⟶ⁿN = step⟶ L M⟶ⁿN L⟶M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⟶ⁿ N
    ------
  → M ⟶ⁿ N
begin M⟶ⁿN = M⟶ⁿN

max : ℕ → ℕ → ℕ
max n m with n ≤? m
... | yes _ = m
... | no  _ = n

height : Type → ℕ
height τ = 0
height (A ⇒ B) = max (height A) (height B) + 1

data Redex : ∀ {Γ A} → Γ ⊢ A → Set where
  red : ∀ {Γ A B} {t : Γ , B ⊢ A} {s : Γ ⊢ B} → Redex ((ƛ t) · s)

-- redex? : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Set
-- redex? (` x) s = {!!}
-- redex? (ƛ t) s = {!!}
-- redex? (t · t₁) s = {!!}
-- redex? (t ⟪ t₁ ⟫) s = {!!}

degree : ∀ {Γ A} {t : Γ ⊢ A} → Redex t → ℕ
degree {Γ} {A} {(ƛ t') · s} (red {Γ} {A} {B}) = height (B ⇒ A)

Sᵢ : ∀ {Γ A} → ℕ → Γ ⊢ A → Γ ⊢ A
Sᵢ d (` x) = ` x
Sᵢ d (ƛ t) = ƛ Sᵢ d t
Sᵢ d ((ƛ t) · s) with degree (red {t = t} {s = s}) ≟ d
... | yes _ = ((Sᵢ d t) [ Sᵢ d s ]) ⟪ Sᵢ d s ⟫
... | no  _ = (ƛ Sᵢ d t) · Sᵢ d s
Sᵢ d (t · s) = Sᵢ d t · Sᵢ d s
Sᵢ d (t ⟪ s ⟫) = Sᵢ d t ⟪ Sᵢ d s ⟫

maxdeg : ∀ {Γ A} → Γ ⊢ A → ℕ
maxdeg (` x) = 0
maxdeg (ƛ t) = maxdeg t
maxdeg ((ƛ t) · s) =
  max (max (maxdeg t) (maxdeg s)) (degree (red {t = t} {s = s}))
maxdeg (t · s) = max (maxdeg t) (maxdeg s)
maxdeg (t ⟪ s ⟫) = max (maxdeg t) (maxdeg s)

S* : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
S* t = S*' t (maxdeg t)
  where
  S*' : ∀ {Γ A} → Γ ⊢ A → ℕ → Γ ⊢ A
  S*' t zero = t
  S*' t (suc n) = S*' (Sᵢ (suc n) t) n

infix 3 _▹_

data _▹_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  φ : ∀ {Γ A B} {t : Γ ⊢ A} {s : Γ ⊢ B}
      -----------
    → t ⟪ s ⟫ ▹ t

infix  2 _▹⁺_
infix  1 ▹begin_
infixr 2 _▹⟨_⟩_
infix  3 _∎▹

data _▹⁺_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎▹ : {t : Γ ⊢ A} {s : Γ ⊢ A}
    → t ▹  s
      ------
    → t ▹⁺ s

  step—▹ : (t : Γ ⊢ A) {s r : Γ ⊢ A}
    → s ▹⁺ r
    → t ▹  s
      ------
    → t ▹⁺ r

pattern _▹⟨_⟩_ t t▹s s▹⁺r = step—▹ t s▹⁺r t▹s

▹begin_ : ∀ {Γ A} {t s : Γ ⊢ A}
  → t ▹⁺ s
    ------
  → t ▹⁺ s
▹begin t▹⁺s = t▹⁺s

infix  2 _⟶⁼_
infix  3 _∎⁼

data _⟶⁼_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎⁼ : (t : Γ ⊢ A)
      ------
    → t ⟶⁼ t

  step—⁼ : (t : Γ ⊢ A) {s r : Γ ⊢ A}
    → s ⟶⁼ r
    → t ⟶  s
      ------
    → t ⟶⁼ r

