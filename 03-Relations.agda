module 03-Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

import Data.Nat as Nat
open Nat using (ℕ; zero; suc; _+_)

import 02-Induction as Ind
open Ind using (+-identityʳ; +-suc; +-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
        ---------
      → zero ≤ n

  s≤s : ∀ {m n : ℕ}
      →    m ≤ n
        -------------
      → suc m ≤ suc n

infix 4 _≤_

≤-refl : ∀ {n : ℕ}
         ---------
       →   n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀ {m n p : ℕ} → m ≤ n
                        → n ≤ p
                          -----
                        → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s {m} {n} m≤n) (s≤s {n} {p} n≤p) = s≤s (≤-trans m≤n n≤p)
-- La joda acá es que hicimos inducción en las pruebas

≤-antisym : ∀ {m n : ℕ} → m ≤ n
                        → n ≤ m
                          -----
                        → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
-- Interesante lo implícito de los parámetros:
-- ¿Significa "los vas a sacar de las mismas pruebas"?

data Total (m n : ℕ) : Set where

  forward : m ≤ n
            ---------
          → Total m n

  flipped : n ≤ m
            ---------
          → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
-- Sin pensar demasiado en la definición que acabo de dar, voy a ver si probarlo
-- me da el insight que me gustaría tener
-- Ok sí ya me lo dio. O me di cuenta. Total es una propiedad (¿proposición?)
-- que se cumple para dos números si uno es ≤ que el otro o viceversa.
-- ≤-total es la propiedad de que vale para todo par de números y por lo tanto
-- los números son totales con respecto a ≤.
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n)
  with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n
                            -----
                          → m + p ≤ n + p
+-monoˡ-≤ m n zero m≤n
  rewrite +-identityʳ m
        | +-identityʳ n
  = m≤n
+-monoˡ-≤ m n (suc p) m≤n
  rewrite +-suc m p
        | +-suc n p
  = s≤s (+-monoˡ-≤ m n p m≤n)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q
                            -----
                          → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q
  = p≤q
+-monoʳ-≤ (suc n) p q p≤q
  = s≤s (+-monoʳ-≤ n p q p≤q)

+-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n
                           → p ≤ q
                             -------------
                           → m + p ≤ n + q
+-mono-≤ {m} {n} {p} {q} m≤n p≤q
  = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
