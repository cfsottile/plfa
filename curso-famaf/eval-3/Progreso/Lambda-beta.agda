module Lambda-beta where

open import Common

infix  4 _⊢_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A} →  Γ ∋ A
                  -----
               →  Γ ⊢ A

  ƛ_ : ∀ {Γ A B} →  Γ , A ⊢ B
                    ---------
                 →  Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B} →  Γ ⊢ A ⇒ B   →   Γ ⊢ A
                     ----------------------
                  →          Γ ⊢ B

rename : ∀ {Γ Δ} →  (∀ {A}  →  Γ ∋ A  →  Δ ∋ A)
                    ---------------------------
                 →   ∀ {A}  →  Γ ⊢ A  →  Δ ⊢ A
rename ρ (` n) = ` ρ n
rename ρ (ƛ t) = ƛ rename (ext ρ) t
rename ρ (t · s) = (rename ρ t) · (rename ρ s)

exts : ∀ {Γ Δ} →  (∀ {A}    →      Γ ∋ A  →      Δ ⊢ A)
                  -------------------------------------
               →   ∀ {A B}  →  Γ , B ∋ A  →  Δ , B ⊢ A
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ} →  (∀ {A}  →  Γ ∋ A  →  Δ ⊢ A)
                   --------------------------
                →   ∀ {A}  →  Γ ⊢ A  →  Δ ⊢ A
subst σ (` n) = σ n
subst σ (ƛ t) = ƛ subst (exts σ) t
subst σ (t · s) = (subst σ t) · (subst σ s)

_[_] : ∀ {Γ A B} →  Γ , B ⊢ A  →  Γ ⊢ B
                    ---------------------
                 →         Γ ⊢ A
_[_] {Γ} {A} {B} t s = subst σ t
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z = s
  σ (S x) = ` x

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {t : Γ , A ⊢ B} → Value (ƛ t)
  -- V-ƛ : ∀ {Γ A B} {V : Γ , A ⊢ B} → Value V → Value (ƛ V)

infix 2 _⟶_

data _⟶_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  β-ƛ : ∀ {Γ A B} {t : Γ , A ⊢ B} {s : Γ ⊢ A}
      --------------------------
    → (ƛ t) · s ⟶ t [ s ]

  -- ξ-ƛ : ∀ {Γ A B} {t t' : Γ , A ⊢ B}
  --   →   t ⟶ t'
  --     -----------
  --   → ƛ t ⟶ ƛ t'

  ξ-·₁ : ∀ {Γ A B} {t t' : Γ ⊢ A ⇒ B} {s : Γ ⊢ A}
    →     t ⟶ t'
      ---------------
    → t · s ⟶ t' · s

  ξ-·₂ : ∀ {Γ A B} {t : Γ ⊢ A ⇒ B} {s s' : Γ ⊢ A}
    →     s ⟶ s'
      ---------------
    → t · s ⟶ t · s'

data Progress : ∀ {Γ A} (t : Γ ⊢ A) → Set where
  step : ∀ {Γ A} {t s : Γ ⊢ A} → t ⟶ s → Progress t
  done : ∀ {Γ A} {t : Γ ⊢ A} → Value t → Progress t

progress : ∀ {A} → (t : ∅ ⊢ A) → Progress t
progress (ƛ t) = done V-ƛ
progress (t · s) with progress t | progress s
... | step Rt | _ = step (ξ-·₁ Rt)
... | _ | step Rs = step (ξ-·₂ Rs)
... | done V-ƛ | done Vs = step β-ƛ
