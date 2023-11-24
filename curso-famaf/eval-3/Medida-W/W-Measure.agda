module W-Measure where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _>_; s≤s; _≤?_; _≟_)
open import Data.Product using (∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
  renaming (subst to sssubst)

open import Common
open import Lambda using (_⊢ᵦ_; `ᵦ_; ƛᵦ_; _·ᵦ_; _⟶ᵦ_;  β-ƛᵦ; ξ-ƛᵦ; ξ-·₁; ξ-·₂; _⟶ᵦⁿ_; _[_]ᵦ)
open import LambdaG
open import Properties
open import AuxProperties

w : ∀ {Γ A} → Γ ⊢ A → ℕ
w (` x) = 0
w (ƛ t) = w t
w (t · s) = w t + w s
w (t ⟪ s ⟫) = w t + w s + 1

W : ∀ {Γ A} → Γ ⊢ᵦ A → ℕ
W t = w (S* (toG t))

postulate
  lemita : ∀ {Γ A B} {t : Γ , A ⊢ᵦ B} {s : Γ ⊢ᵦ A}
    → toG t [ toG s ] ≡ toG (t [ s ]ᵦ)
  ⟶-▹ : ∀ {Γ A} {t s : Γ ⊢ᵦ A} {t′ : Γ ⊢ A}
    → t ⟶ᵦ s → (toG t) ⟶ t′ → t′ ▹ (toG s)
  ▹⁺-w : ∀ {Γ A} {t s : Γ ⊢ A} → t ▹⁺ s → w t > w s
  ⟶-S* : ∀ {Γ A} {t s : Γ ⊢ A} → t ⟶ s → S* t ≡ S* s
  ▹⁺-S* : ∀ {Γ A} {t s : Γ ⊢ A} → t ▹⁺ s → S* t ▹⁺ S* s

-- Lemitas para el teorema
postulate
  W-ƛ-comm : ∀ {Γ A B} {t s : Γ , A ⊢ᵦ B} → W t > W s → W (ƛᵦ t) > W (ƛᵦ s)
  W-·₁-comm : ∀ {Γ A B} {t t′ : Γ ⊢ᵦ A ⇒ B} {s : Γ ⊢ᵦ A}
    → W t > W t′ → W (t ·ᵦ s) > W (t′ ·ᵦ s)
  W-·₂-comm : ∀ {Γ A B} {t : Γ ⊢ᵦ A ⇒ B} {s s′ : Γ ⊢ᵦ A}
    → W s > W s′ → W (t ·ᵦ s) > W (t ·ᵦ s′)

-- Teorema
W-decreasing : ∀ {Γ A} {t s : Γ ⊢ᵦ A} → t ⟶ᵦ s → W t > W s
W-decreasing {Γ} {A} {(ƛᵦ t) ·ᵦ s} .{t [ s ]ᵦ} (β-ƛᵦ {Γ} {B} {A}) = S5
  where
  r = toG ((ƛᵦ t) ·ᵦ s)
  r′ = toG t [ toG s ] ⟪ toG s ⟫
  u = toG t [ toG s ]
  u′ = toG (t [ s ]ᵦ)
  u≡u′ = lemita {Γ} {B} {A} {t} {s}
  S1 : S* r ≡ S* r′
  S1 = ⟶-S* {t = r} {s = r′} β-ƛ
  S2 : S* r′ ▹⁺ S* u
  S2 = ▹⁺-S* {Γ} {A} {r′} {u} (φ ∎▹)
  S3 : w (S* r′) > w (S* u)
  S3 = ▹⁺-w S2
  S4 : w (S* r) > w (S* u)
  S4 rewrite S1 = S3
  S5 : W ((ƛᵦ t) ·ᵦ s) > W (t [ s ]ᵦ)
  S5 rewrite sym u≡u′ = S4
W-decreasing {Γ} {A₁ ⇒ A₂} {ƛᵦ t} {ƛᵦ s} (ξ-ƛᵦ R)
  = W-ƛ-comm {Γ} {A₁} {A₂} {t} {s} (W-decreasing R)
W-decreasing {Γ} {A} {t ·ᵦ s} {t′ ·ᵦ .s} (ξ-·₁ {Γ} {B} {A} R)
  = W-·₁-comm {Γ} {B} {A} {t} {t′} {s} (W-decreasing R)
W-decreasing {Γ} {A} {t ·ᵦ s} {.t ·ᵦ s′} (ξ-·₂ {Γ} {B} {A} R)
  = W-·₂-comm {Γ} {B} {A} {t} {s} {s′} (W-decreasing R)
