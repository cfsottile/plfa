open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_ : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_ : Term → Term → Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_ : Id → Term → Term

-- Unos ejemplines
two : Term
two = `suc `suc `zero

plus : Term
plus =
  μ "+" ⇒ ƛ "n" ⇒ ƛ "m" ⇒
    case ` "n" [zero⇒ ` "m" |suc "n" ⇒ `suc (` "+" · ` "n" · ` "m") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "n" ⇒ ƛ "m" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "n" · ` "s" · (` "m" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc ` "n"

mul : Term
mul = μ "*" ⇒ ƛ "n" ⇒ ƛ "m" ⇒
  case ` "n" [zero⇒ `zero |suc "n" ⇒ plus · ` "m" · (` "*" · ` "n" · ` "m") ]

mulᶜ : Term
mulᶜ = ƛ "n" ⇒ ƛ "m" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "n" · (` "m" · ` "s") · ` "z"

data Value : Term → Set where

  V-ƛ : ∀ {x N}
        -------------
      → Value (ƛ x ⇒ N)

  V-zero :
         -----------
         Value `zero

  V-suc : ∀ {V}
        → Value V
          -------------
        → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]
(P · M) [ y := V ] = P [ y := V ] · M [ y := V ]
`zero [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
case P [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _ = case P [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case P [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]

binder-subst : Id → (Id → Term → Term) → Term → Id → Term → Term
binder-subst x tmk M y N with x ≟ y
... | yes _ = tmk x M
... | no  _ = tmk x N

_[_:=_]' : Term → Id → Term → Term
(` x) [ y := V ]' = binder-subst x (λ _ x → x) V y (` x)
(ƛ x ⇒ N) [ y := V ]' = binder-subst x (ƛ_⇒_) N y (N [ y := V ]')
(P · M) [ y := V ]' = P [ y := V ]' · M [ y := V ]'
`zero [ y := V ]' = `zero
(`suc M) [ y := V ]' = `suc M [ y := V ]'
case P [zero⇒ M |suc x ⇒ N ] [ y := V ]' =
  case P [ y := V ]' [zero⇒ M [ y := V ]'
                     |suc x ⇒ binder-subst x (λ _ x → x) N y (N [ y := V ]') ]
(μ x ⇒ N) [ y := V ]' = binder-subst x (μ_⇒_) N y (N [ y := V ]')

-- _ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]'
--       ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
-- _ = refl

-- _ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]' ≡ sucᶜ · (sucᶜ · `zero)
-- _ = refl

-- _ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]' ≡ ƛ "x" ⇒ `zero
-- _ = refl

-- _ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]' ≡ ƛ "x" ⇒ ` "x"
-- _ = refl

-- _ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]' ≡ ƛ "y" ⇒ ` "y"
-- _ = refl

infix 4 _⟶_

data _⟶_ : Term → Term → Set where

  ξ-·₁ : ∀ {M M' N}
       → M ⟶ M'
         ----------------
       → M · N ⟶ M' · N

  ξ-·₂ : ∀ {V M M'}
       → M ⟶ M'
         ----------------
       → V · M ⟶ V · M'

  β-ƛ : ∀ {x N V}
         ----------------
       → (ƛ x ⇒ N) · V ⟶ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M ⟶ M′
      ------------------
    → `suc M ⟶ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L ⟶ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] ⟶ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] ⟶ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] ⟶ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M ⟶ M [ x := μ x ⇒ M ]

-- _ : Set
-- _ = twoᶜ · sucᶜ · `zero  ⟶ `suc (`suc `zero)

infix 2 _—↠_
infix 1 begin_
infixr 2 _⟶⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M → M —↠ M

  step-→ : ∀ M {M' N}
         → M' —↠ N
         → M ⟶ M'
           -------
         → M —↠ N

pattern _⟶⟨_⟩_ M M⟶M' M'—↠N = step-→ M M'—↠N M⟶M'

begin_ : ∀ {M N}
       → M —↠ N
         ------
       → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
        → M ⟶ N
          -------
        → M —↠′ N

  refl′ : ∀ {M}
          -------
        → M —↠′ M

  trans′ : ∀ {M N P}
         → M —↠′ N
         → N —↠′ P
           -------
         → M —↠′ P

-- —↠≲—↠′ : ∀ {M N} → M —↠ N ≲ (M —↠′ N)
-- —↠≲—↠′ = record { to = to ; from = from ; from∘to = from∘to }
--   where
--     to : ∀ {M N} → M —↠ N → M —↠′ N
--     to (M ∎) = refl′
--     to (M ⟶⟨ R ⟩ S) = trans′ (step′ R) (to S)

--     from : ∀ {M N} → M —↠′ N → M —↠ N
--     from (step′ {M} {N} R) = step-→ M (N ∎) R
--     from (refl′ {M}) = M ∎
--     from (trans′ {M} R S) with from R | from S
--     ... | step-→ M R₂ R₁ | S' = {!!}
--     -- ... | step-→ M {M'} U T | step-→ P U' T' =
--     --   M ⟶⟨ T ⟩ (M' ⟶⟨ {!!} ⟩ {!!})
--     -- ... | step-→ M U T | _ ∎ = M ⟶⟨ T ⟩ U
--     -- ... | _ ∎ | step-→ M U T = M ⟶⟨ T ⟩ U
--     -- ... | _ ∎ | _ ∎ = M ∎

--     from∘to : ∀ {M N} (x : M —↠ N) → from (to x) ≡ x
--     from∘to = {!!}

postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      ---------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L ⟶ M) × (L ⟶ N))
      ----------------------
    → ∃[ P ] ((M ⟶ P) × (N ⟶ P))

postulate
  deterministic : ∀ {L M N}
    → L ⟶ M
    → L ⟶ N
      -------
    → M ≡ N

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5 _,_∶_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (Γ , x ∶ A) = (x , A) ∷ to Γ
    from : List (Id × Type) → Context
    from [] = ∅
    from ((x , A) ∷ xs) = from xs , x ∶ A
    from∘to : (c : Context) → from (to c) ≡ c
    from∘to ∅ = refl
    from∘to (Γ , x ∶ A) rewrite from∘to Γ = refl
    to∘from : (xs : List (Id × Type)) → to (from xs) ≡ xs
    to∘from [] = refl
    to∘from ((x , A) ∷ xs) rewrite to∘from xs = refl

infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      -----------------
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
      -----------------
    → Γ , y ∶ B ∋ x ∶ A

S′ : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ∶ A
      -----------------
    → Γ , y ∶ B ∋ x ∶ A
S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ∶ A
      -----------
    → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ∶ A  ⊢  N  ∶ B
      ------------------
    → Γ  ⊢  ƛ x ⇒ N  ∶  A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
      -------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      -------------
    → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ∶ `ℕ
      ---------------
    → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ `ℕ ⊢ N ∶ A
      ------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  -- μ : ∀ {Γ x M A}
  ⊢μ : ∀ {Γ x A M}
    → Γ , x ∶ A ⊢ M ∶ A
      ----------------
    → Γ ⊢ μ x ⇒ M ∶ A

postulate ⊢plus : ∀ {Γ} → Γ ⊢ plus ∶ `ℕ ⇒ `ℕ ⇒ `ℕ

⊢mul : ∀ {Γ} → Γ ⊢ mul ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S′ Z))
  ⊢zero (⊢plus · ⊢` (S′ Z) · (((⊢` (S′ (S′ (S′ Z)))) · ⊢` Z) · ⊢` (S′ Z))))))

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢mulᶜ : ∀ {Γ A} → Γ ⊢ mulᶜ ∶ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ ((⊢` (S′ (S′ (S′ Z)))) · ((⊢` (S′ (S′ Z))) · ⊢` (S′ Z)) · ⊢` Z))))
