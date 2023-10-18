module 07-Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc)
open import 03-Relations using (_<_; _≤_; z≤n; s≤s; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import 06-Connectives using (_×_; ⟨_,_⟩; →-distrib-⊎; _⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; _∘_)

¬_ : Set → Set
¬ A = A → ⊥

-- Interesante: en la explicación dice que una evidencia de ¬ A es una función λ
-- x → N con N : ⊥ y x ∈ FV(N)

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    ------
  → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()
-- Esto es trivial porque Agda ve que 1 y 2 simplifican a formas normales
-- distintas y por lo tanto no puede construirse evidencia de 1 ≡ 2.

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()
-- Se hace un pattern sobre las posibles evidencias de que zero ≡ suc m, que son
-- ninguna

id : ⊥ → ⊥
id x = x

id' : ⊥ → ⊥
id' ()

id≡id' : id ≡ id'
id≡id' = extensionality λ ()
-- La joda es que no hay ningún elemento en el dominio de id/id' así que la prop
-- id x ≡ id' x vale trivialmente. Y eso se expresa con el patrón (). O sea que
-- las funciones tienen una similaridad interesante con los para todo?

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))
-- Acá flashé que por beta ¬x y ¬x' aplicados con x me iban a dar ⊥. Pero no,
-- porque ⊥ no tiene habitantes, no hay formas normales. Hay que verlo por
-- lógica digamos. Tampoco. Queremos ver que dos pruebas de una negación son
-- iguales. Para eso usamos extensionalidad, o sea vemos que al tomar un
-- argumento son iguales. Pero al tener una prueba de ¬x y tomar un x, tenemos
-- una contradicción y podemos probar cualquier cosa.

<-irreflexive : ∀ {n : ℕ} → ¬ n < n
-- <-irreflexive {zero} ()
<-irreflexive {suc n} (s<s n<n) = <-irreflexive n<n

data Trichotomy (m n : ℕ) : Set where
  lesser : m < n → ¬ m ≡ n → ¬ n < m → Trichotomy m n
  equal : ¬ m < n → m ≡ n → ¬ n < m → Trichotomy m n
  greater : ¬ m < n → ¬ m ≡ n → n < m → Trichotomy m n

≡-suc : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
≡-suc refl = refl

-- -- metí cambios y voy a usar mi propia def de <
-- trichotomy : ∀ {m n : ℕ} → Trichotomy m n
-- trichotomy {zero} {zero} = equal <-irreflexive refl <-irreflexive
-- trichotomy {zero} {suc n} = lesser (s≤s z≤n) (λ ()) λ ()
-- trichotomy {suc m} {zero} = greater (λ ()) (λ ()) (s≤s z≤n)
-- trichotomy {suc m} {suc n}
--   with trichotomy {m} {n}
--   -- Muy interesante lo que descubrí. En algun momento pensé en meter un with
--   -- para forzar patrones y cosas. Y resulta que haciendo un PM sobre la prueba,
--   -- como la única posibilidad es refl, de ahí en más es todo lo mismo ALV
-- ... | lesser m<n ¬m≡n ¬m>n = lesser (s≤s m<n) (λ{ refl → ¬m≡n refl }) {!!}
-- ... | equal ¬m<n m≡n ¬m>n = equal (λ{ (s≤s sm≤n) → {!!} }) (cong suc m≡n) {!!}
-- ... | greater ¬m<n ¬m≡n m>n = greater {!!} (λ { refl → ¬m≡n refl }) (s≤s m>n)

trichotomy : ∀ {m n : ℕ} → Trichotomy m n
trichotomy {zero} {zero} = equal <-irreflexive refl <-irreflexive
trichotomy {zero} {suc n} = lesser z<s (λ ()) λ ()
trichotomy {suc m} {zero} = greater (λ ()) (λ ()) z<s
trichotomy {suc m} {suc n}
  with trichotomy {m} {n}
... | lesser m<n ¬m≡n ¬n<m = lesser (s<s m<n)
                                    (λ{ refl → ¬m≡n refl })
                                    λ{ (s<s n<m) → ¬n<m n<m }
... | equal ¬m<n m≡n ¬n<m = equal (λ{ (s<s m<n) → ¬m<n m<n })
                                  (cong suc m≡n)
                                  λ{ (s<s n<m) → ¬n<m n<m }
... | greater ¬m<n ¬m≡n n<m = greater (λ{ (s<s m<n) → ¬m<n m<n })
                                      (λ { refl → ¬m≡n refl })
                                      (s<s n<m)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

-- ⊎-dual-× = record
--   { to = λ ¬a⊎b → ⟨ (λ a → ¬a⊎b (inj₁ a)) , ¬a⊎b ∘ inj₂ ⟩
--   ; from = λ { ⟨ ¬a , ¬b ⟩ → λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b } }
--   ; from∘to = λ ¬a⊎b → extensionality λ { (inj₁ a) → refl ; (inj₂ b) → refl }
--   -- no queda claro por qué funciona con refl acá
--   ; to∘from = λ{ ⟨ ¬a , ¬b ⟩ → refl }
--   }

×-dual-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ (inj₁ ¬a) ⟨ a , b ⟩ = ¬a a
×-dual-⊎ (inj₂ ¬b) ⟨ a , b ⟩ = ¬b b

-- Esto parece no ser demostrable constructivamente
-- to : ∀ {A B : Set} → (A × B → ⊥) → (A → ⊥) ⊎ (B → ⊥)
-- to a×b→⊥ = {!!}

-- ×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- ×-dual-⊎ = record
--   { to = λ ¬a×b → {!!}
--   ; from = λ{ (inj₁ ¬a) → λ{ ⟨ a , b ⟩ → ¬a a }
--             ; (inj₂ ¬b) → λ{ ⟨ a , b ⟩ → ¬b b } }
--   ; from∘to = {!!}
--   ; to∘from = {!!}
--   }

module Classical where

  postulate
    em : ∀ {A : Set} → A ⊎ ¬ A

  em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
  em-irrefutable p = p (inj₂ λ a → p (inj₁ a))
  -- em-irrefutable ¬-a⊎¬a = ¬-a⊎¬a (inj₂ λ a → ¬-a⊎¬a (inj₁ a))

  postulate
    dne : ∀ {A : Set} → ¬ ¬ A → A
    pl : ∀ {A B : Set} → ((A → B) → A) → A
    iad : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
    dm : ∀ {A B : Set} → ¬ ((¬ A) × (¬ B)) → A ⊎ B

  em→dne : ∀ {A : Set} → A ⊎ ¬ A → ¬ ¬ A → A
  em→dne (inj₁ a) ¬¬a = a
  em→dne (inj₂ ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

  -- em→dne' : ∀ {A : Set} → A ⊎ ¬ A → ∀ {A : Set} → ¬ ¬ A → A
  -- em→dne' (inj₁ a) ¬¬a = {!!}
  -- em→dne' (inj₂ ¬a) ¬¬a = {!!}

  dne→pl : ∀ {A B : Set} → (¬ ¬ A → A) → ((A → B) → A) → A
  dne→pl ¬¬a→a a→b_→a = ¬¬a→a λ ¬a → {!!}

  pl→iad : ∀ {A B : Set} → (((A → B) → A) → A) → (A → B) → ¬ A ⊎ B
  pl→iad pl a→b = {!!}

  iad→dm : ∀ {A B : Set} → ((A → B) → ¬ A ⊎ B) → ¬ ((¬ A) × (¬ B)) → A ⊎ B
  iad→dm p q = {!!}

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable (¬¬¬a) = ¬¬¬-elim ¬¬¬a

postulate dm' : ∀ {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
×-stable : ∀ {A B : Set} → (¬ ¬ A → A) → (¬ ¬ B → B) → Stable (A × B)
×-stable sa sb ¬¬-a×b = ⟨ {!!} , {!!} ⟩
