module 08-Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
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

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ----------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

-- hacer yo
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to = ∃-elim
  ; from = λ f a ba → f ⟨ a , ba ⟩
  ; from∘to = λ f → refl
  ; to∘from = λ f → ∀-extensionality λ{ ⟨ a , ba ⟩ → refl }
  }
-- WTF generalización de la curryficiación???????

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to = λ{ ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
          ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩ }
  ; from = λ{ (inj₁ ⟨ a , ba ⟩) → ⟨ a , inj₁ ba ⟩
            ; (inj₂ ⟨ a , ca ⟩) → ⟨ a , inj₂ ca ⟩ }
  ; from∘to = λ{ ⟨ a , inj₁ ba ⟩ → refl ; ⟨ a , inj₂ ca ⟩ → refl }
  ; to∘from = λ{ (inj₁ ⟨ a , ba ⟩) → refl ; (inj₂ ⟨ a , ca ⟩) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ ba , ca ⟩ ⟩ = ⟨ ⟨ a , ba ⟩ , ⟨ a , ca ⟩ ⟩

∃-⊎ : ∀ {A : Set} {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = record
  { to = λ{ ⟨ aa , baa ⟩ → inj₁ baa
          ; ⟨ bb , bbb ⟩ → inj₂ (inj₁ bbb)
          ; ⟨ cc , bcc ⟩ → inj₂ (inj₂ bcc) }
  ; from = λ{ (inj₁ baa ) → ⟨ aa , baa ⟩
            ; (inj₂ (inj₁ bbb)) → ⟨ bb , bbb ⟩
            ; (inj₂ (inj₂ bcc)) → ⟨ cc , bcc ⟩ }
  ; from∘to = λ{ ⟨ aa , baa ⟩ → refl
               ; ⟨ bb , bbb ⟩ → refl
               ; ⟨ cc , bcc ⟩ → refl }
  ; to∘from = λ{ (inj₁ baa ) → refl
               ; (inj₂ (inj₁ bbb)) → refl
               ; (inj₂ (inj₂ bcc)) → refl }
  }

-- TO DO even-odd

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = record
  { to = λ f a ba → f ⟨ a , ba ⟩
  ; from = λ{ f ⟨ a , ba ⟩ → f a ba }
  ; from∘to = λ ¬f → ∀-extensionality λ{ ⟨ a , ba ⟩ → refl }
  ; to∘from = λ y → refl
  }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬ba ⟩ f = ¬ba (f a)
