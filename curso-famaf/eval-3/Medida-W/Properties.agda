module Properties where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; s≤s; _≤?_; _≟_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Common
open import Lambda using (_⊢ᵦ_; `ᵦ_; ƛᵦ_; _·ᵦ_; _⟶ᵦ_;  β-ƛᵦ; ξ-ƛᵦ; ξ-·₁; ξ-·₂; _⟶ᵦⁿ_; _[_]ᵦ)
open import LambdaG

postulate
  confluence : ∀ {Γ A} {t s r u : Γ ⊢ A}
    → ((t ⟶ⁿ s) × (t ⟶ⁿ r))
      ---------------------
    → ∃[ u ] ((s ⟶ⁿ u) × (r ⟶ⁿ u))

-- Lemas para Sᵢ-reduct
⟶ⁿ→ξ-ƛ : ∀ {Γ A B} {t s : Γ , A ⊢ B} {d : ℕ} → t ⟶ⁿ s → ƛ t ⟶ⁿ ƛ s
⟶ⁿ→ξ-ƛ {Γ} {A} {B} {t} {.t} {d} (.t ∎) = ƛ t ∎
⟶ⁿ→ξ-ƛ {Γ} {A} {B} {t} {s} {d} (step⟶ .t {t′} {.s} R′ R)
  with ⟶ⁿ→ξ-ƛ {Γ} {A} {B} {t′} {s} {d} R′
... | S = step⟶ (ƛ t) {ƛ t′} {ƛ s} S (ξ-ƛ R)

⟶ⁿ→ξ-· : ∀ {Γ A B} (t t′ : Γ ⊢ A ⇒ B) (s s′ : Γ ⊢ A) (d : ℕ)
  → t ⟶ⁿ t′ → s ⟶ⁿ s′ → t · s ⟶ⁿ t′ · s′
⟶ⁿ→ξ-· {Γ} {A} {B} t .t s .s d (.t ∎) (.s ∎) = t · s ∎
⟶ⁿ→ξ-· {Γ} {A} {B} t .t s s″ d (.t ∎) (step⟶ .s {s′} {.s″} R′ R)
  with ⟶ⁿ→ξ-· t t s′ s″ d (t ∎) R′
... | S = step⟶ (t · s) {t · s′} {t · s″} S (ξ-·₂ R)
⟶ⁿ→ξ-· {Γ} {A} {B} t t″ s .s d (step⟶ .t {t′} {.t″} R′ R) (.s ∎)
  with ⟶ⁿ→ξ-· t′ t″ s s d R′ (s ∎)
... | S = step⟶ (t · s) {t′ · s} {t″ · s} S (ξ-·₁ R)
⟶ⁿ→ξ-· {Γ} {A} {B} t t″ s s″ d
  (step⟶ .t {t′} {.t″} Rt′ Rt) (step⟶ .s {s′} {.s″} Rs′ Rs)
  with ⟶ⁿ→ξ-· t′ t″ s′ s″ d Rt′ Rs′
... | R = step⟶ (t · s) {t′ · s} {t″ · s″}
          (step⟶ (t′ · s) {t′ · s′} {t″ · s″} R (ξ-·₂ Rs)) (ξ-·₁ Rt)

-- Sᵢ-reduct : ∀ {Γ A} {t : Γ ⊢ A} → (d : ℕ) → t ⟶ⁿ Sᵢ d t
-- Sᵢ-reduct {Γ} {A} {` x} d = ` x ∎
-- Sᵢ-reduct {Γ} {A ⇒ B} {ƛ t} d =
--   ⟶ⁿ→ξ-ƛ {Γ} {A} {B} {t} {Sᵢ d t} {d} (Sᵢ-reduct {Γ , A} {B} {t} d)
-- -- Acá quiero tratar estos casos por separado según la aplicación sea un redex o
-- -- no. Para eso hice Dec (t ≡ s) pero parece que no sirve.
-- Sᵢ-reduct {Γ} {A} {(ƛ t) · s} d = {!!}
-- Sᵢ-reduct {Γ} {A} {t · s} d
--   with Sᵢ-reduct {Γ} {_ ⇒ A} {t} d | Sᵢ-reduct {Γ} {_} {s} d
-- ... | R | S = {!!} -- ⟶ⁿ→ξ-· t (Sᵢ d t) s (Sᵢ d s) d R S
-- Sᵢ-reduct {Γ} {A} {t ⟪ t₁ ⟫} d = {!!}

data isƛ : ∀ {Γ A} (t : Γ ⊢ A) → Set where
  ƛ_ : ∀ {Γ A B} → (t : Γ , A ⊢ B) → isƛ t

-- Lemas de simplificación (Sᵢ y S*)
postulate
  -- subst de términos de menor altura no crea ƛ
  ƛ-creation-subst : ∀ {Γ A B} (t : Γ , A ⊢ B) (s : Γ ⊢ A)
    → ¬ (isƛ t) → height A < height B → ¬ (isƛ (t [ s ]))
  -- Sᵢ no crea ƛ
  ƛ-creation-simp : ∀ {Γ A} (t : Γ ⊢ A) (d : ℕ)
    → ¬ (isƛ t) → maxdeg t ≤ d → d ≤ height A → ¬ (isƛ (Sᵢ d t))
  -- subst no incrementa maxdeg
  inc-maxdeg-subst : ∀ {Γ A B} (t : Γ , A ⊢ B) (s : Γ ⊢ A) (d : ℕ)
    → maxdeg t < d → maxdeg s < d → height A < d → maxdeg (t [ s ]) < d
  -- Sᵢ reduce maxdeg
  inc-maxdeg-simp : ∀ {Γ A} (t : Γ ⊢ A) (d : ℕ)
    → maxdeg t ≤ d → maxdeg (Sᵢ d t) < d
  -- t reduce a su simplificación completa
  S*-reduct : ∀ {Γ A} {t : Γ ⊢ A} → t ⟶ⁿ S* t
  -- simplificación completa es normalización
  S*-nf : ∀ {Γ A} {t : Γ ⊢ A} → Value (S* t)

-- Lemas de conmutación de ▹ y ⟶
postulate
  comm-▹⁺-⟶ⁿ : ∀ {Γ A} {t s t′ s′ : Γ ⊢ A}
    → t ▹⁺ s
    → t ⟶ⁿ t′
    → ∃[ s′ ]((t′ ▹⁺ s′) × (s ⟶ⁿ s′))
  local-comm-▹-⟶ⁿ : ∀ {Γ A} {t s t′ s′ : Γ ⊢ A}
    → t ▹ s
    → t ⟶ t′
    → ∃[ s′ ]((t′ ▹⁺ s′) × (s ⟶⁼ s′))
  local-comm→comm : ∀ {Γ A} {t s t′ s′ : Γ ⊢ A}
    → (t ▹ s → t ⟶ t′ → ∃[ s′ ]((t′ ▹⁺ s′) × (s ⟶⁼ s′)))
    → t ▹⁺ s → t ⟶ⁿ t′ → ∃[ s′ ]((t′ ▹⁺ s′) × (s ⟶ⁿ s′))
