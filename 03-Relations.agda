module 03-Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

import Data.Nat as Nat
open Nat using (ℕ; zero; suc; _+_; _*_)

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
  rewrite +-identityʳ m | +-identityʳ n
  = m≤n
+-monoˡ-≤ m n (suc p) m≤n
  rewrite +-suc m p | +-suc n p
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

*-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n
                           → p ≤ q
                             -----
                           → m * p ≤ n * q
*-mono-≤ z≤n p≤q = z≤n
*-mono-≤ {suc m} {suc n} {p} {q} (s≤s m≤n) p≤q
  rewrite +-comm p (m * p) | +-comm q (n * q)
  = +-mono-≤ (*-mono-≤ m≤n p≤q) p≤q

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
        ---------
      → zero < suc n

  s<s : ∀ {m n : ℕ}
      → m < n
        -------------
      → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n
                        → n < p
                          -----
                        → m < p
<-trans z<s (s<s n<p) = z<s
<-trans {suc m} {suc n} {suc p} (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where
  lesser  : m < n → Trichotomy m n
  equal   : m ≡ n → Trichotomy m n
  greater : n < m → Trichotomy m n

<-tricho : ∀ (m n : ℕ) → Trichotomy m n
<-tricho zero zero = equal refl
<-tricho zero (suc n) = lesser z<s
<-tricho (suc m) zero = greater z<s
<-tricho (suc m) (suc n)
  with <-tricho m n
...  | lesser  m<n = lesser (s<s m<n)
...  | equal   m≡n = equal (cong suc m≡n)
...  | greater n<m = greater (s<s n<m)

-- Versiones con inducción en otros datos

-- <-+-suc : ∀ {m n : ℕ} → m < m + suc n
-- <-+-suc {zero} = z<s
-- <-+-suc {suc m} = s<s <-+-suc

-- +-monoʳ-< : ∀ {m n p : ℕ}
--   → m < n
--     -------------
--   → m + p < n + p
-- +-monoʳ-< {zero} {suc n} {p} z<s
--   rewrite +-comm n p
--         | sym (+-suc p n)
--   = <-+-suc
-- +-monoʳ-< (s<s m<n) = s<s (+-monoʳ-< m<n)

-- +-monoˡ-< : ∀ {n p q : ℕ}
--   → p < q
--     -------------
--   → n + p < n + q
-- +-monoˡ-< {n} z<s
--   rewrite +-identityʳ n
--   = <-+-suc
-- +-monoˡ-< {n} {suc p} {suc q} (s<s p<q)
--   rewrite +-suc n p
--         | +-suc n q
--   = s<s (+-monoˡ-< p<q)

+-monoˡ-< : ∀ {n p q : ℕ}
  → p < q
    -------------
  → n + p < n + q
+-monoˡ-< {zero} p<q = p<q
+-monoˡ-< {suc n} p<q = s<s (+-monoˡ-< p<q)

+-monoʳ-< : ∀ {m n p : ℕ}
  → m < n
    -------------
  → m + p < n + p
+-monoʳ-< {m} {n} {zero} m<n
  rewrite +-identityʳ m
        | +-identityʳ n
  = m<n
+-monoʳ-< {m} {n} {suc p} m<n
  rewrite +-suc m p
        | +-suc n p
  = s<s (+-monoʳ-< m<n)

+-mono-< : ∀ {m n p q : ℕ}
  → m < n
  → p < q
    -------------
  → m + p < n + q
-- En otras noticias, dándole un poco menos de vueltas, la joda con usar la
-- transitividad es simplemente haberse dado cuenta de que n+p queda en el medio
-- de los dos sublemas. O haberse dado cuenta de que hay un n+p en el medio y a
-- partir de eso armar los sublemas.
+-mono-< m<n p<q = <-trans (+-monoʳ-< m<n) (+-monoˡ-< p<q)

≤→< : ∀ {m n : ℕ}
  → suc m ≤ n
    -----
  → m < n
≤→< {zero} {suc n'} (s≤s m≤n') = z<s
≤→< {suc m} {suc n'} (s≤s m≤n') = s<s (≤→< m≤n')

<→≤ : ∀ {m n : ℕ}
  → m < n
    ---------
  → suc m ≤ n
<→≤ z<s = s≤s z≤n
<→≤ (s<s m<n) = s≤s (<→≤ m<n)

≤-n-suc : ∀ {n : ℕ} → n ≤ suc n
≤-n-suc {zero} = z≤n
≤-n-suc {suc n} = s≤s ≤-n-suc

<-trans' : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans' {m} {n} {p} m<n n<p =
-- suc m ≤ n ≤ suc n ≤ p
  ≤→< {m} {p}
    (≤-trans {suc m} {suc n} {p}
      (≤-trans {suc m} {n} {suc n}
        (<→≤ m<n) ≤-n-suc) (<→≤ n<p))

<-trans'' : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans'' m<n n<p = ≤→< (≤-trans (≤-trans (<→≤ m<n) ≤-n-suc) (<→≤ n<p))

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
    ---------
    even zero

  suc : ∀ {n : ℕ}
    → odd n
      -----------
    → even (suc n)

data odd where

  suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)
o+o≡e (suc {m} em) (suc {n} en) rewrite +-suc m n = suc (suc (e+e≡e em en))
-- muy fumado esto de mezclar todo
