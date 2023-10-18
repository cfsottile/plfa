import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.part1.Isomorphism.≃-Reasoning

{-
Agda knows that any value of type ⊤′ must be tt′, so any time we need a value of type ⊤′, we can tell Agda to figure it out:
truth′ : ⊤′
truth′ = _
Y por qué no puede darse cuenta de lo mismo con ⊤ si hay un solo constructor?
-}

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

infixr 1 _⊎_

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = case-⊎ inj₂ inj₁
  ; from = case-⊎ inj₂ inj₁
  ; from∘to = λ{ (inj₁ a) → refl ; (inj₂ b) → refl }
  ; to∘from = λ{ (inj₁ b) → refl ; (inj₂ a) → refl }
  }

⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc = record
  { to = λ{ (inj₁ a) → inj₁ (inj₁ a)
          ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
          ; (inj₂ (inj₂ c)) → inj₂ c }
  ; from = λ{ (inj₁ (inj₁ a)) → inj₁ a
            ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
            ; (inj₂ c) → inj₂ (inj₂ c) }
  ; from∘to = λ{ (inj₁ a) → refl
               ; (inj₂ (inj₁ b)) → refl
               ; (inj₂ (inj₂ c)) → refl }
  ; to∘from = λ{ (inj₁ (inj₁ a)) → refl
               ; (inj₁ (inj₂ b)) → refl
               ; (inj₂ c) → refl }
  }

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → A ≃ ⊥ ⊎ A
⊥-identityˡ = record
  { to = inj₂
  ; from = λ{ (inj₁ ⊥) → ⊥-elim ⊥ ; (inj₂ a) → a }
  ; from∘to = λ x → refl
  ; to∘from = λ{ (inj₁ ⊥) → ⊥-elim ⊥ ; (inj₂ a) → refl }
  }

⊥-identityʳ : ∀ {A : Set} → A ≃ A ⊎ ⊥
⊥-identityʳ = record
  { to = inj₁
  ; from = λ{ (inj₂ ⊥) → ⊥-elim ⊥ ; (inj₁ a) → a }
  ; from∘to = λ x → refl
  ; to∘from = λ{ (inj₂ ⊥) → ⊥-elim ⊥ ; (inj₁ a) → refl }
  }

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

-- Preguntar a Miguel: cuándo reduce λx.fx a f como para dar el goal f ≡ f
-- Considerando que pedirle a Agda que normalice λ x → f x da el mismo término
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    -- ; to∘from =  λ y → extensionality {!!}
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }


→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    ; from = λ{ ( ⟨ a→c , b→c ⟩ ) → λ{ (inj₁ a) → a→c a ; (inj₂ b) → b→c b }}
    ; from∘to = λ f → extensionality λ{ (inj₁ a) → refl ; (inj₂ b) → refl}
    -- ; from∘to = λ f → extensionality ?
    -- Acá extensionality dice dame un x a ver si son todos iguales, y mostralo
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
  ; from = λ{ ⟨ f , g ⟩ a → ⟨ f a , g a ⟩ }
  ; from∘to = λ f → extensionality λ a → η-× (f a)
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to      = λ { ⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩
                ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩ }
  ; from    = λ { (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩
                ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩ }
  ; from∘to = λ { ⟨ inj₁ a , c ⟩ → refl
                ; ⟨ inj₂ b , c ⟩ → refl }
  ; to∘from = λ { (inj₁ ⟨ a , c ⟩) → refl
                ; (inj₂ ⟨ b , c ⟩) → refl }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× {A} {B} {C} = record { to = to' ; from = from' ; from∘to = from∘to' }
  where
    to' : (A × B) ⊎ C → (A ⊎ C) × (B ⊎ C)
    to' (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
    to' (inj₂     c    ) = ⟨ inj₂ c , inj₂ c ⟩
    from' : (A ⊎ C) × (B ⊎ C) → (A × B) ⊎ C
    from' ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
    from' ⟨ inj₁ a , inj₂ c ⟩ = inj₂ c
    from' ⟨ inj₂ c , _ ⟩ = inj₂ c
    -- ¿Por qué me marca esto? Ah, debe ser porque no sabe si _ es inj₁ o inj₂. Y
    -- cuando especifico inj₁ a , inj₂ c ... Ah, no. Porque entonces es un
    -- problema también no saber si el _ de ⟨ inj₂ c , _ ⟩ es inj₁ o inj₂.
    -- ¿Quizá hay algo con que el segundo elemento pueda depender del primero?
    -- PREGUNTAR A MIGUEL
    -- from' ⟨ _ , inj₂ c ⟩ = inj₂ c
    from∘to' : (x : (A × B) ⊎ C) → from' (to' x) ≡ x
    from∘to' (inj₁ ⟨ a , b ⟩) = refl
    from∘to' (inj₂     c    ) = refl

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

-- La corresponding dist-law es (A ⊎ B) × (A ⊎ C) ≃ A ⊎ (B × C). Cuando A 

postulate
  ⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
