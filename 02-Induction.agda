module 02-Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m) + n + p
  ≡⟨⟩
    (suc (m + n)) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    (suc m) + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) =
  begin
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n rewrite +-suc n m | cong suc (+-comm m n) = refl

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    m + (n + p) + q
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p)
                   | cong (_+ p) (+-comm m n)
                   | +-assoc n m p = refl

*-distr-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distr-+ zero n p = refl
*-distr-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distr-+ m n p) ⟩
    p + ((m * p) + (n * p))
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + (n * p)
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distr-+ n (m * n) p
                          | cong ((n * p) +_) (*-assoc m n p) = refl

*-absorventʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-absorventʳ zero = refl
*-absorventʳ (suc m) rewrite *-absorventʳ m = refl

*-suc : ∀ (n m : ℕ) → n * suc m ≡ n + n * m
*-suc zero m = refl
*-suc (suc n) m =
  begin
    suc n * suc m
  ≡⟨⟩
    suc m + (n * suc m)
  ≡⟨⟩
    suc (m + (n * suc m))
  ≡⟨ cong suc (cong (m +_) (*-suc n m)) ⟩
    suc (m + (n + n * m))
  ≡⟨ cong suc (+-comm m (n + n * m)) ⟩
    suc ((n + n * m) + m)
  ≡⟨⟩
    suc (n + n * m) + m
  ≡⟨⟩
    suc n + n * m + m
  ≡⟨ +-assoc (suc n) (n * m) m ⟩
    suc n + (n * m + m)
  ≡⟨ cong (suc n +_) (+-comm (n * m) m) ⟩
    suc n + (m + n * m)
  ≡⟨⟩
    suc n + (suc n * m)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-absorventʳ n = refl
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (*-suc n m) ⟩
    n * suc m
  ∎

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero zero p = refl
∸-+-assoc zero (suc n) p rewrite 0∸n≡0 p = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

-- _^_ : ℕ → ℕ → ℕ
-- m ^ zero = 1
-- m ^ (suc n) = m * (m ^ n)

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite cong (m *_) (^-distribˡ-+-* m n p)
                                 | *-assoc m (m ^ n) (m ^ p)
                                 = refl

^-distribʳ-+-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-+-* m n zero = refl
^-distribʳ-+-* m n (suc p)
  rewrite cong ((m * n) *_) (^-distribʳ-+-* m n p)
        = begin
          (m * n) * ((m ^ p) * (n ^ p))
        ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩
          ((m * n) * (m ^ p)) * (n ^ p)
        ≡⟨ cong (_* (n ^ p)) (*-assoc m n (m ^ p)) ⟩
          (m * (n * (m ^ p))) * (n ^ p)
        ≡⟨ cong (_* (n ^ p)) (cong (m *_)  (*-comm n (m ^ p))) ⟩
          (m * ((m ^ p) * n)) * (n ^ p)
        ≡⟨ *-assoc m ((m ^ p) * n) (n ^ p) ⟩
          m * (((m ^ p) * n) * (n ^ p))
        ≡⟨ cong (m *_) (*-assoc (m ^ p) n (n ^ p)) ⟩
          m * ((m ^ p) * (n * (n ^ p)))
        ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
          (m * (m ^ p)) * (n * (n ^ p))
        ∎

^-absorventˡ : ∀ (m : ℕ) → 1 ^ m ≡ 1
^-absorventˡ zero = refl
^-absorventˡ (suc m) rewrite cong (_+ zero) (^-absorventˡ m) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p rewrite ^-absorventˡ p = refl
^-*-assoc m (suc n) p rewrite ^-distribʳ-+-* m (m ^ n) p
                            | ^-distribˡ-+-* m p (n * p)
                            | cong ((m ^ p) *_) (^-*-assoc m n p)
                            = refl

{- Nota sobre 28/8/23: estuvimos viendo que cong permite meterse en un ≡, pero
no en un ≤ -}
{-
Profundizo considerando lo que creo que entendí ahora. ≡ es una relación entre
términos. `cong` es la función que me permite meter el ≡ adentro de otros
~~constructores~~ funciones. Bueno no es "meter" el ≡, es probar que se preserva
agregando cualquier constructor a cada lado. Estaría bueno implementar el cong.

Por otro lado en +-mono-≤ nos pasa que queremos meter ≡ en ≤. O sea, queremos
ver que si n ≡ p y m ≤ n, vale m ≤ p
VER NOTA TABLET: Notas Agda
-}
