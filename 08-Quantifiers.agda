module 08-Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
open import Function using (_∘_)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
  { to = λ f → ⟨ (λ x → proj₁ (f x)) , proj₂ ∘ f ⟩
  ; from = λ{ ⟨ f , g ⟩ x → ⟨ f x , g x ⟩ }
  ; from∘to = λ f → refl
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }
-- This proposition is possibly a generalization of →-distrib-×, since A → B is
-- a particular case of ∀ (x : A) → B x, when x does not occur free in B. This
-- is then the dependent case of the distributivity isomorphism. It would be
-- interesting to see an example of two types that are provable isomorphic using
-- the ∀ case but not the →. The difference is that the → cannot have the
-- consequents depending on an antecedent's element.

-- data Vec (A : Set) : (n : ℕ) → Set where
--   nil : Vec A 0
--   cons : ∀ (n : ℕ) → A → Vec A n → Vec A (suc n)

-- p1 : ∀ (A : Set) → ℕ → Set
-- p1 A n = ∀-distrib-× {ℕ} {Vec A} {Vec A}

-- Lo dejamos para ver con Fidel

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g

-- The converse (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- does not hold. Consider the predicates even and odd. For every natural it is
-- true that one of them hold, while for neither is is true that it holds for
-- every natural.

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
      ---------
    → f ≡ g

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× = record
  { to = λ Bη → ⟨ Bη aa , ⟨ (Bη bb) , (Bη cc) ⟩ ⟩
  ; from = λ{ ⟨ Ba , ⟨ Bb , Bc ⟩ ⟩ → λ{ aa → Ba ; bb → Bb ; cc → Bc } }
  ; from∘to = λ Bη → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl }
  ; to∘from = λ x → refl
  }

-- hacer yo
-- ∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
--   → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
