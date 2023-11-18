module 12-Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

V¬—→ : ∀ {M N} → Value M → ¬ (M —→ N)
V¬—→ V-ƛ ()
V¬—→ V-zero ()
V¬—→ (V-suc v) (ξ-suc R) = V¬—→ v R

—→¬V : ∀ {M N} → M —→ N → ¬ Value M
—→¬V R VM = V¬—→ VM R

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      ----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero : Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      -----------------
    → Canonical `suc V ⦂ `ℕ

Canonical≃ClosedValues : ∀ {V A} → Canonical V ⦂ A ≃ (∅ ⊢ V ⦂ A) × (Value V)
Canonical≃ClosedValues {V} {A} =
  record { to =  to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : ∀ {V} → Canonical V ⦂ A → ∅ ⊢ V ⦂ A × Value V
    to (C-ƛ π) = ⟨ ⊢ƛ π , V-ƛ ⟩
    to C-zero = ⟨ ⊢zero , V-zero ⟩
    to (C-suc c) with to c
    ... | ⟨ t , v ⟩ = ⟨ (⊢suc t) , (V-suc v) ⟩

    from : ∀ {V A} → ∅ ⊢ V ⦂ A × Value V → Canonical V ⦂ A
    from ⟨ ⊢ƛ t , V-ƛ ⟩ = C-ƛ t
    from ⟨ ⊢zero , V-zero ⟩ = C-zero
    from ⟨ ⊢suc t , V-suc v ⟩ = C-suc (from ⟨ t , v ⟩)

    from∘to : ∀ {V} → (c : Canonical V ⦂ A) → from (to c) ≡ c
    from∘to (C-ƛ x) = refl
    from∘to C-zero = refl
    from∘to (C-suc c) rewrite from∘to c = refl

    to∘from : ∀ {V} → (cv : ∅ ⊢ V ⦂ A × Value V) → to (from cv) ≡ cv
    to∘from ⟨ ⊢ƛ t , V-ƛ ⟩ = refl
    to∘from ⟨ ⊢zero , V-zero ⟩ = refl
    to∘from ⟨ ⊢suc t , V-suc v ⟩ rewrite to∘from ⟨ t , v ⟩ = refl

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
       Value M
       ----------
     → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢ƛ ⊢N) = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step RL = step (ξ-·₁ RL)
... | done V-ƛ with progress ⊢M
...   | step RM = step (ξ-·₂ V-ƛ RM)
...   | done VM = step (β-ƛ VM)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step RM = step (ξ-suc RM)
... | done VM = done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step RL = step (ξ-case RL)
... | done V-zero = step β-zero
... | done (V-suc VL) = step (β-suc VL)
progress (⊢μ ⊢M) = step β-μ

Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ {M} =
  record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : ∀ {M} → Progress M → Value M ⊎ ∃[ N ](M —→ N)
    to (step {N} R) = inj₂ ⟨ N , R ⟩
    to (done VM) = inj₁ VM

    from : ∀ {M} → Value M ⊎ ∃[ N ](M —→ N) → Progress M
    from (inj₁ VM) = done VM
    from (inj₂ ⟨ N , R ⟩) = step R

    from∘to : ∀ {M} → (p : Progress M) → from (to p) ≡ p
    from∘to (step x) = refl
    from∘to (done x) = refl

    to∘from : ∀ {M} → (s : Value M ⊎ ∃-syntax (_—→_ M)) → to (from s) ≡ s
    to∘from (inj₁ VM) = refl
    to∘from (inj₂ ⟨ N , R ⟩) = refl

progress' : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress' .(ƛ _ ⇒ _) (⊢ƛ ⊢M) = inj₁ V-ƛ
progress' (M · N) (⊢M · ⊢N) with progress' M ⊢M
... | inj₂ ⟨ M' , R ⟩ = inj₂ ⟨ M' · N , ξ-·₁ R ⟩
... | inj₁ (V-ƛ {x} {M'}) with progress' N ⊢N
...   | inj₁ VN = inj₂ ⟨ M' [ x := N ] , β-ƛ VN ⟩
...   | inj₂ ⟨ N' , R ⟩ = inj₂ ⟨ (M · N') , ξ-·₂ V-ƛ R ⟩
progress' .`zero ⊢zero = inj₁ V-zero
progress' (`suc M) (⊢suc ⊢M) with progress' M ⊢M
... | inj₁ VM = inj₁ (V-suc VM)
... | inj₂ ⟨ M' , R ⟩ = inj₂ ⟨ `suc M' , ξ-suc R ⟩
progress' (case L [zero⇒ M |suc x ⇒ N ]) (⊢case ⊢L ⊢M ⊢N) with progress' L ⊢L
... | inj₁ V-zero = inj₂ ⟨ M , β-zero ⟩
... | inj₁ (V-suc {L'} VL') = inj₂ ⟨ N [ x := L' ] , β-suc VL' ⟩
... | inj₂ ⟨ L' , R ⟩ = inj₂ ⟨ case L' [zero⇒ M |suc x ⇒ N ] , ξ-case R ⟩
progress' (μ x ⇒ M) (⊢μ ⊢M) = inj₂ ⟨ M [ x := μ x ⇒ M ] , β-μ ⟩

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | step R = no (—→¬V R)
... | done VM = yes VM

-- Renombre

ext : ∀ {Γ Δ}
  → (∀ {x A}     →          Γ ∋ x ⦂ A  →          Δ ∋ x ⦂ A)
    ------------------------------------
  → ∀ {x y A B}  →  Γ , y ⦂ B ∋ x ⦂ A  →  Δ , y ⦂ B ∋ x ⦂ A
ext Γ→Δ Z = Z
ext Γ→Δ (S x≢y p) = S x≢y (Γ→Δ p)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ---------------------------------
  →  ∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A
rename ρ (⊢` Γ∋x) = ⊢` (ρ Γ∋x)
rename ρ (⊢ƛ ⊢M) = ⊢ƛ (rename (ext ρ) ⊢M)
rename ρ (⊢M · ⊢N) = rename ρ ⊢M · rename ρ ⊢N
rename ρ ⊢zero = ⊢zero
rename ρ (⊢suc ⊢M) = ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢M ⊢M₁ ⊢M₂) =
  ⊢case (rename ρ ⊢M) (rename ρ ⊢M₁) (rename (ext ρ) ⊢M₂)
rename ρ (⊢μ ⊢M) = ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ---------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename (λ ()) ⊢M

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    -------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {y C}
    → Γ , x ⦂ A , x ⦂ B ∋ y ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ y ⦂ C
  ρ Z = Z
  ρ (S x≢x Z) = ⊥-elim (x≢x refl)
  ρ (S x≢y (S x≢y' p)) = S x≢y p

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    -------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z = S x≢y Z
  ρ (S x≢z Z) = Z
  ρ (S x≢z (S y≢z p)) = S y≢z (S x≢z p)
