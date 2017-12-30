-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of functional properties
-- Copyright (C) 2017 Beren Oguz
--
-- This program is free software: you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program.  If not, see <https://www.gnu.org/licenses/>.

module Math.Function where
  open import Math.Logic using (_∧_; ∃; _≡_; ∃!)
  open import Math.NaturalNumbers using (ℕ; _′)
  
  infixl 31 _^_
  infixr 30 _∘_
  infixl 29 _←_

  id : ∀ {n} {A : Set n} → A → A
  id x = x
  
  _∘_ : ∀ {n} {A B C : Set n} → (B → C) → (A → B) → (A → C)
  f ∘ g = λ x → f (g x)

  _←_ : ∀ {A B : Set} → (A → B) → A → B
  f ← a = f a

  _^_ : ∀ {n} {A : Set n} → (A → A) → ℕ → (A → A)
  f ^ 0 = id
  f ^ (n ′) = f ∘ f ^ n

  Binary-Operation : ∀ {n} → Set n → Set n → Set n → Set n
  Binary-Operation A B C = A → B → C

  Associative : ∀ {n} {A : Set n} → Binary-Operation A A A → Set n
  Associative F = ∀ {x y z} → F (F x y) z ≡ F x (F y z)

  Commutative : ∀ {n} {A B : Set n} → Binary-Operation A A B → Set n
  Commutative F = ∀ {x y} → F x y ≡ F y x

  Identity : ∀ {A : Set} → Binary-Operation A A A → Set
  Identity F = ∃ e , ∀ {x} → (F x e ≡ x) ∧ (F e x ≡ x)

  Unique-Identity : ∀ {A : Set} → Binary-Operation A A A → Set
  Unique-Identity F = ∃! e , ∀ {x} → (F x e ≡ x) ∧ (F e x ≡ x)

  Inverse : ∀ {A : Set} → (F : Binary-Operation A A A) → Identity F → Set
  Inverse F record {witness = e} = ∀ {x} → ∃ x⁻¹ , (F x x⁻¹ ≡ e) ∧ (F x⁻¹ x ≡ e)

  Unique-Inverse : ∀ {A : Set} → (F : Binary-Operation A A A) → Identity F → Set
  Unique-Inverse F record {witness = e} = ∀ {x} → ∃! x⁻¹ , (F x x⁻¹ ≡ e) ∧ (F x⁻¹ x ≡ e)

  Injection : ∀ {S T} → (S → T) → Set
  Injection φ = ∀ {x y z} → (φ x ≡ z) ∧ (φ y ≡ z) → x ≡ y

  Surjection : ∀ {S T} → (S → T) → Set
  Surjection φ = ∀ {y} → ∃ x , (φ x ≡ y)

  record Bijection {S T} (F : S → T) : Set where
    field
      injective : Injection F
      surjective : Surjection F
