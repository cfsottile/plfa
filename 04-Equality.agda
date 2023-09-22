module 04-Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
       -----
     → x ≡ x
  x ∎ = refl

open ≡-Reasoning

{-
module ≤-Reasoning where
  import Data.Nat as Nat
  open Nat using (ℕ; zero; suc; _+_; _*_)

  import 03-Relations as Rel
  open Rel using (_≤_; z≤n; s≤s; ≤-refl; ≤-trans)

  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≡⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≡ y
    → y ≤ z
      -----
    → x ≤ z
  x ≡⟨ refl ⟩ y≤z = y≤z

  _∎ : ∀ (x : ℕ)
       -----
     → x ≤ x
  x ∎ = ≤-refl

-- no, no es cierto esto; necesito mono-suc
  -- ≤-cong : (f : ℕ → ℕ) → {x y : ℕ} → x ≤ y → f x ≤ f y
  -- ≤-cong f {zero} {y} z≤n = {!!}
  -- ≤-cong f {suc _} {suc _} (s≤s x≤y) = {!!}
-- open ≤-Reasoning

-- module Ejemplin where
--   open ≤-Reasoning

  postulate
    +-comm : ∀ {m n : ℕ} → m + n ≡ n + m

  +-monoʳ-≤ : ∀ {n p q : ℕ} → p ≤ q → n + p ≤ n + q
  +-monoʳ-≤ {zero} {p} {q} p≤q =
    begin
      zero + p
    ≡⟨ refl ⟩
      p
    ≤⟨ p≤q ⟩
      q
    ≡⟨ refl ⟩
      zero + q
    ∎
  +-monoʳ-≤ {suc n} {p} {q} p≤q =
    begin
      suc n + p
    ≤⟨ s≤s (+-monoʳ-≤ p≤q) ⟩
      suc n + q
    ∎

  +-monoˡ-≤ : ∀ {m n p : ℕ} → m ≤ n → m + p ≤ n + p
  +-monoˡ-≤ {m} {n} {p} m≤n =
    begin
      m + p
    ≡⟨ +-comm {m} {p} ⟩
      p + m
    ≤⟨ +-monoʳ-≤ {p} {m} {n} m≤n ⟩
      p + n
    ≡⟨ +-comm {p} {n} ⟩
      n + p
    ∎

  -- mono-suc : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
  -- mono-suc m≤n = s≤s {!!}

  +-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
  +-mono-≤ m≤n p≤q = {!!}
-}

{-# BUILTIN EQUALITY _≡_ #-}

import 01-Naturals as Nat
open Nat using (ℕ; zero; suc; _+_; _*_)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev rewrite +-comm m n = ev

even-comm' : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm' m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl = ev

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' zero n with n + zero | +-identity n
...               | .(n)     | refl         = refl
+-comm' (suc m) n with n + suc m      | +-suc n m
...                  | .(suc (n + m)) | refl with m + n      | +-comm' m n
...                                             | .(n + m)   | refl         = refl

-- +-comm' (suc m) n with   m + n  | +-comm' n m
-- ...                  | .(n + m) | +-suc n m        = ?

-- +-comm' (suc m) n with   m + n  | +-comm' m n
-- ...                  | .(n + m) | refl        = sym (+-suc n m)

-- ...                  | .(n + m) | +-suc n m
-- ...                  | .(n + suc m) | refl   = {!!}

-- +-comm' (suc m) n with  suc (m + n) | +-suc m n
-- ...                  | .(m + suc n) | _                        = {!!}

-- Leibniz equality

_≐_ : ∀ {A : Set} → (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
-- Dados un elemento A de Set₀ y dos elementos x e y de A, da un elemento de
-- Set₁: la proposición que toma un predicado de A en Set₀ y una prueba de P x,
-- y da una prueba de P y.

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = x≐y Q Qx
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
-- Toda Q que vale para x, vale para y por x≐y. Q z = P z → P x vale para x por
-- refl-≐, ∴ vale para y, i.e. vale Q y = P y → P x

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
-- ≡-implies-≐ x≡y P = subst P x≡y
≡-implies-≐ x≡y P x rewrite x≡y = x

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = x≐y Q Qx
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
