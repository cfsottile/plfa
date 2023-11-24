module AuxProperties where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; s≤s; _≤?_; _≟_)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)

open import Common
open import Lambda using (_⊢ᵦ_; `ᵦ_; ƛᵦ_; _·ᵦ_; _⟶ᵦ_;  β-ƛᵦ; ξ-ƛᵦ; ξ-·₁; ξ-·₂; _⟶ᵦⁿ_; _[_]ᵦ)
open import LambdaG

fromG : ∀ {Γ A} (t : Γ ⊢ A) → Γ ⊢ᵦ A
fromG (` x) = `ᵦ x
fromG (ƛ t) = ƛᵦ fromG t
fromG (t · s) = fromG t ·ᵦ fromG s
fromG (t ⟪ s ⟫) = fromG t

toG : ∀ {Γ A} → Γ ⊢ᵦ A → Γ ⊢ A
toG (`ᵦ x) = ` x
toG (ƛᵦ t) = ƛ toG t
toG (t ·ᵦ s) = toG t · toG s

⊢ᵦ≲⊢ : ∀ {Γ A} → Γ ⊢ᵦ A ≲ Γ ⊢ A
⊢ᵦ≲⊢ = record { to = toG ; from = fromG ; from∘to = from∘to }
  where
  from∘to : ∀ {Γ A} → (t : Γ ⊢ᵦ A) → fromG (toG t) ≡ t
  from∘to (`ᵦ x) = refl
  from∘to (ƛᵦ t) rewrite from∘to t = refl
  from∘to (t ·ᵦ s) rewrite from∘to t | from∘to s = refl

_≡∋?_ : ∀ {Γ A} (x y : Γ ∋ A) → Dec (x ≡ y)
Z ≡∋? Z = yes refl
Z ≡∋? (S y) = no λ ()
(S x) ≡∋? Z = no λ ()
(S x) ≡∋? (S y) with x ≡∋? y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }

_≡T?_ : (A B : Type) → Dec (A ≡ B)
τ ≡T? τ = yes refl
τ ≡T? (B ⇒ B₁) = no λ ()
(A ⇒ A₁) ≡T? τ = no λ ()
(A ⇒ A₁) ≡T? (B ⇒ B₁) with A ≡T? B | A₁ ≡T? B₁
... | yes refl | yes refl = yes refl
... | no  A≢B | _ = no λ { refl → A≢B refl }
... | _ | no  A₁≢B₁ = no λ { refl → A₁≢B₁ refl }

_⊢≡?_ : ∀ {Γ A} (t s : Γ ⊢ A) → Dec (t ≡ s)
(` x) ⊢≡? (` y) with x ≡∋? y
... | yes refl = yes refl
... | no  x≢y  = no λ { refl → x≢y refl }
(` x) ⊢≡? (ƛ s) = no λ ()
(` x) ⊢≡? (s · s₁) = no λ ()
(` x) ⊢≡? (s ⟪ s₁ ⟫) = no λ ()
(ƛ t) ⊢≡? (` x) = no λ ()
(ƛ t) ⊢≡? (ƛ s) with t ⊢≡? s
... | yes refl = yes refl
... | no  t≢s = no λ{ refl → t≢s refl }
(ƛ t) ⊢≡? (s · s₁) = no λ ()
(ƛ t) ⊢≡? (s ⟪ s₁ ⟫) = no λ ()
(t · t₁) ⊢≡? (` x) = no λ ()
(t · t₁) ⊢≡? (ƛ s) = no λ ()
(_·_ {Γ} {A} {B} t₁ t₂) ⊢≡? (_·_ {Γ} {A′} {B} s₁ s₂) with A ≡T? A′
... | no A≢A′ = no λ{ refl → A≢A′ refl }
... | yes refl with t₁ ⊢≡? s₁ | t₂ ⊢≡? s₂
... | yes refl | yes refl = yes refl
... | no  t₁≢s₁ | _ = no λ{ refl → t₁≢s₁ refl }
... | _ | no t₂≢s₂ = no λ{ refl → t₂≢s₂ refl }
(t · t₁) ⊢≡? (s ⟪ s₁ ⟫) = no λ ()
(t ⟪ t₁ ⟫) ⊢≡? (` x) = no λ ()
(t ⟪ t₁ ⟫) ⊢≡? (ƛ s) = no λ ()
(t ⟪ t₁ ⟫) ⊢≡? (s · s₁) = no λ ()
(_⟪_⟫ {Γ} {A} {B} t s) ⊢≡? (_⟪_⟫ {Γ} {A} {B′} t′ s′) with B ≡T? B′
... | no B≢B′ = no λ{ refl → B≢B′ refl }
... | yes refl with t ⊢≡? t′ | s ⊢≡? s′
... | yes refl | yes refl = yes refl
... | no  t≢t′ | _ = no λ{ refl → t≢t′ refl }
... | _ | no  s≢s′ = no λ{ refl → s≢s′ refl }

