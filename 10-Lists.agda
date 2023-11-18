import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n; _<_; _≤?_; _<?_)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; +-suc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)
open import Data.Maybe using (Maybe; just; nothing)

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data List' : Set → Set where
  []'   : ∀ {A : Set} → List' A
  _∷'_ : ∀ {A : Set} → A → List' A → List' A

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
-- ++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

length : ∀ {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ∎

-- reverse-++-distrib' : ∀ {A : Set} (xs ys : List A)
--   → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
-- reverse-++-distrib' [] ys = sym (++-identityʳ (reverse ys))
-- reverse-++-distrib' (x ∷ xs) ys =
--   -- cong (_++ [ x ]) (reverse-++-distrib xs ys)
--   ++-assoc (reverse ys) (reverse xs) [ x ]

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node t₁ x t₂) = node (map-Tree f g t₁) (g x) (map-Tree f g t₂)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} → (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A)
    -----------------------
  → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  trans (cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y))
        (sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y))

foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs ys : List A)
    --------------------------------------------------------
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
-- Me mareé con los tipos. foldr ... ⊗ foldr ... une dos A con ⊗.
foldr-monoid-++ _⊗_ e ⊗-monoid xs ys =
  trans (foldr-++ _⊗_ e xs ys)
        (foldr-monoid _⊗_ e ⊗-monoid xs (foldr _⊗_ e ys))

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ acc [] = acc
foldl _⊗_ acc (x ∷ xs) = foldl _⊗_ (acc ⊗ x) xs

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
      ---------
    → f ≡ g

lemma : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (x : A) (xs : List A)
  → x ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ (e ⊗ x) xs
lemma _⊗_ e ⊗-monoid x [] =
  trans (identityʳ ⊗-monoid x) (sym (identityˡ ⊗-monoid x))
lemma _⊗_ e ⊗-monoid x (x₁ ∷ xs) =
  begin
    x ⊗ foldl _⊗_ (e ⊗ x₁) xs
  ≡⟨ cong (x ⊗_) (sym (lemma _⊗_ e ⊗-monoid x₁ xs)) ⟩
    x ⊗ (x₁ ⊗ foldl _⊗_ e xs)
  ≡⟨ sym (assoc ⊗-monoid x x₁ (foldl _⊗_ e xs)) ⟩
    (x ⊗ x₁) ⊗ foldl _⊗_ e xs
  ≡⟨ lemma _⊗_ e ⊗-monoid (x ⊗ x₁) xs ⟩
    foldl _⊗_ (e ⊗ (x ⊗ x₁)) xs
  ≡⟨ cong (_$ xs) (cong (foldl _⊗_ $_) (sym (assoc ⊗-monoid e x x₁))) ⟩
    foldl _⊗_ ((e ⊗ x) ⊗ x₁) xs
  ∎

foldr-monoid-foldl-lemma : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → (xs : List A)
    -------------------------------
  → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl-lemma _⊗_ e ⊗-monoid [] = refl
foldr-monoid-foldl-lemma _⊗_ e ⊗-monoid (x ∷ xs) =
  begin
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-lemma _⊗_ e ⊗-monoid xs) ⟩
    (x ⊗ foldl _⊗_ e xs)
  ≡⟨ lemma _⊗_ e ⊗-monoid x xs ⟩
    foldl _⊗_ (e ⊗ x) xs
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid =
  ∀-extensionality (foldr-monoid-foldl-lemma _⊗_ e ⊗-monoid)

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} →     P x  → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in = λ{ (here ())
          ; (there (here ()))
          ; (there (there (here ())))
          ; (there (there (there (here ()))))
          ; (there (there (there (there ())))) }
-- No me termina de cerrar cómo sabe que no hay más casos. Bueno, tiene que
-- valer para alguno here, o para [] there. Se pueden observar todos y ver que
-- ninguno cumple.

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ {A} {P} xs ys = record { to = to xs ys ; from = from xs ys }
  where

    to : (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys P++ = ⟨ [] , P++ ⟩
    to (x ∷ xs) ys (px ∷ P++) with to xs ys P++
    ... | ⟨ Pxs , Pys ⟩ = ⟨ px ∷ Pxs , Pys ⟩

    from : (xs ys : List A) → All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

Any-++ʳ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P xs → Any P (xs ++ ys)
Any-++ʳ (x ∷ xs) ys (here Px) = here Px
Any-++ʳ (x ∷ xs) ys (there Pxs) = there (Any-++ʳ xs ys Pxs)

Any-++ˡ : ∀ {A : Set} {P : A → Set} (xs ys : List A) → Any P ys → Any P (xs ++ ys)
Any-++ˡ [] ys Pys = Pys
Any-++ˡ (x ∷ xs) ys Pys = there (Any-++ˡ xs ys Pys)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
  → Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ {A} {P} xs ys = record { to = to xs ys ; from = from xs ys }
  where
    to : (xs ys : List A) → Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys Pys = inj₂ Pys
    to (x ∷ xs) ys (here px) = inj₁ (here px)
    to (x ∷ xs) ys (there P++) with to xs ys P++
    ... | inj₁ Pxs = inj₁ (there Pxs)
    ... | inj₂ Pys = inj₂ Pys

    from : (xs ys : List A) → (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from xs ys (inj₁ Pxs) = Any-++ʳ xs ys Pxs
    from xs ys (inj₂ Pys) = Any-++ˡ xs ys Pys

-- All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
--   → All P (xs ++ ys) ≃ (All P xs × All P ys)
-- All-++-≃ {A} {P} xs ys = record { to = to xs ys ; from = from xs ys
--                                 ; from∘to = from∘to xs ys ; to∘from = to∘from xs ys }
--   where

--     to : (xs ys : List A) → All P (xs ++ ys) → (All P xs × All P ys)
--     to [] ys P++ = ⟨ [] , P++ ⟩
--     to (x ∷ xs) ys (px ∷ P++) with to xs ys P++
--     ... | ⟨ Pxs , Pys ⟩ = ⟨ px ∷ Pxs , Pys ⟩

--     from : (xs ys : List A) → All P xs × All P ys → All P (xs ++ ys)
--     from [] ys ⟨ [] , Pys ⟩ = Pys
--     from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

--     from∘to : (xs ys : List A) (P++ : All P (xs ++ ys))
--       → from xs ys (to xs ys P++) ≡ P++
--     from∘to [] ys P++ = refl
--     from∘to (x ∷ xs) ys (Px ∷ P++) with to xs ys P++
--     ... | ⟨ [] , Pys ⟩ = {!!}
--     ... | ⟨ x₁ ∷ Pxs , Pys ⟩ = {!!}
--     to∘from : (xs ys : List A) (x : All P xs × All P ys) → to xs ys (from xs ys x) ≡ x
--     to∘from = {!!}

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬ Any P xs) ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ {A} {P} xs = record { to = to xs ; from = from xs }
  where

    to : (xs : List A) → (¬ Any P xs) → All (¬_ ∘ P) xs
    to [] ¬Any = []
    to (x ∷ xs) ¬Any = (¬Any ∘ here) ∷ to xs (¬Any ∘ there)

    from : (xs : List A) → All (¬_ ∘ P) xs → (¬ Any P xs)
    from (x ∷ xs) (¬Px ∷ All¬) (here Px) = ¬Px Px
    from (x ∷ xs) (¬Px ∷ All¬) (there Any) = from xs All¬ Any

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs ≃ ∀ x → x ∈ xs → P x
All-∀ {A} {P} xs =
  record { to = to xs ; from = from xs ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : (xs : List A) → All P xs → ∀ x → x ∈ xs → P x
    -- to [] [] x ()
    to (x ∷ _) (Px ∷ Pxs) x (here refl) = Px
    to (_ ∷ xs) (Px ∷ Pxs) x (there x∈xs) = to xs Pxs x x∈xs

    from : (xs : List A) → (∀ x → x ∈ xs → P x) → All P xs
    from [] p = []
    from (x ∷ xs') p = p x (here refl) ∷ from xs' λ x x∈xs' → p x (there x∈xs')

    from∘to : {xs : List A} → (Pxs : All P xs) → from xs (to xs Pxs) ≡ Pxs
    from∘to [] = refl
    from∘to (Px ∷ Pxs') = cong (Px ∷_) (from∘to Pxs')

    lemma' : {xs : List A} → (p : (x : A) → x ∈ xs → P x) → (x : A) → (e : x ∈ xs)
      → to xs (from xs p) x e ≡ p x e
    lemma' {.(x ∷ _)} p x (here refl) = refl
    lemma' {(_ ∷ xs')} p x (there e) = lemma' {xs'} (λ x x∈xs' → p x (there x∈xs')) x e

    to∘from : {xs : List A} → (p : (x : A) → x ∈ xs → P x) → to xs (from xs p) ≡ p
    to∘from p = ∀-extensionality λ x → ∀-extensionality λ e → lemma' p x e

Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ {A} {P} xs = record
  { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : {xs : List A} → Any P xs → ∃[ x ] (x ∈ xs × P x)
    to {x ∷ xs'} (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
    to {_ ∷ xs'} (there e) with to e
    ... | ⟨ x , ⟨ x∈xs' , Px ⟩ ⟩ = ⟨ x , ⟨ there x∈xs' , Px ⟩ ⟩

    from : {xs : List A} → ∃[ x ] (x ∈ xs × P x) → Any P xs
    from {.(x ∷ _)} ⟨ x , ⟨ here refl , Px ⟩ ⟩ = here Px
    from {(_ ∷ xs')} ⟨ x , ⟨ there x∈xs' , Px ⟩ ⟩ =
      there (from ⟨ x , ⟨ x∈xs' , Px ⟩ ⟩)

    from∘to : {xs : List A} (Pxs : Any P xs) → from (to Pxs) ≡ Pxs
    from∘to (here  Px)  = refl
    from∘to (there Pxs) = cong there (from∘to Pxs)

    to∘from : {xs : List A} (∃x : ∃[ x ] (x ∈ xs × P x)) → to (from ∃x) ≡ ∃x
    to∘from {.(x ∷ _)} ⟨ x , ⟨ here refl , Px ⟩ ⟩ = refl
    to∘from {_ ∷ xs'} ⟨ x , ⟨ there x∈xs' , Px ⟩ ⟩
      rewrite to∘from ⟨ x , ⟨ x∈xs' , Px ⟩ ⟩ = refl

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p = foldr (λ x → p x ∧_) true

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P = ∀ (x : A) → Dec (P x)

-- Por qué no escribir
-- Decidable' : ∀ {A : Set} (P : A → Set) (x : A) → Dec (P x)
-- Decidable' P x = ?
-- All?' : ∀ {A : Set} {P : A → Set} {xs : List A} → Decidable' P → Decidable' (All P)

-- Porque Decidable es la Prop que está habitada cuando ∀ x. Dec (P x) está
-- habitada. Y Decidable' es una función que dice cómo obtener un habitante de
-- Dec (P x). Pero no todo P es decidible así que sería imposible construir esa
-- función. Entonces Decidable es una Prop, y All? por ejemplo es la prueba de
-- inhabitation de Decidable con P = All P', asumiendo habitado Decidable P, es
-- decir hay función que para x da prueba de P x o de ¬ (P x).

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with P? x | All? P? xs
... | yes Px | yes Pxs = yes (Px ∷ Pxs)
... | yes Px | no ¬Pxs = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
... | no ¬Px | _       = no λ{ (Px ∷ _) → ¬Px Px }

Any? : ∀ {A : Set} → {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no λ ()
Any? P? (x ∷ xs) with P? x | Any? P? xs
... | yes Px | _ = yes (here Px)
... | no ¬Px | yes Pxs = yes (there Pxs)
... | no ¬Px | no ¬Pxs = no λ{ (here Px) → ¬Px Px ; (there Pxs) → ¬Pxs Pxs }

data merge {A : Set} : (xs ys zs : List A) → Set where

  [] : merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------
    → merge xs (y ∷ ys) (y ∷ zs)

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] (merge xs ys zs × All P xs × All (¬_ ∘ P) ys)
split P? [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (x ∷ zs) with P? x | split P? zs
... | yes Px | ⟨ xs , ⟨ ys , ⟨ zs' , ⟨ Pxs , ¬Pxs ⟩ ⟩ ⟩ ⟩ =
  ⟨ x ∷ xs , ⟨ ys , ⟨ left-∷ zs' , ⟨ Px ∷ Pxs , ¬Pxs ⟩ ⟩ ⟩ ⟩
... | no ¬Px | ⟨ xs , ⟨ ys , ⟨ zs' , ⟨ Pxs , ¬Pxs ⟩ ⟩ ⟩ ⟩ =
  ⟨ xs , ⟨ x ∷ ys , ⟨ right-∷ zs' , ⟨ Pxs , ¬Px ∷ ¬Pxs ⟩ ⟩ ⟩ ⟩
