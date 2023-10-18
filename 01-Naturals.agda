module 01-Naturals where
{-
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
_*_ : ℕ → ℕ → ℕ
_^_ : ℕ → ℕ → ℕ
_∸_ : ℕ → ℕ → ℕ

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
to : ℕ → Bin
from : Bin → ℕ
-}

-- ================================================
--  Natural numbers -- unary
-- ================================================
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Exercise
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

-- ================================================
--  Basic functions on natural numbers
-- ================================================
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ zero  = 1
m ^ suc n = m * (m ^ n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_
infixl 8  _^_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}
