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

  _←_ : ∀ {n m} {A : Set n} {B : Set m} → (A → B) → A → B
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

  Identity : ∀ {n} {A : Set n} → Binary-Operation A A A → Set n
  Identity F = ∃ e , ∀ {x} → (F x e ≡ x) ∧ (F e x ≡ x)

  Unique-Identity : ∀ {n} {A : Set n} → Binary-Operation A A A → Set n
  Unique-Identity F = ∃! e , ∀ {x} → (F x e ≡ x) ∧ (F e x ≡ x)

  Inverse : ∀ {n} {A : Set n} → (F : Binary-Operation A A A) → Identity F → Set n
  Inverse F record {witness = e} = ∀ {x} → ∃ x⁻¹ , (F x x⁻¹ ≡ e) ∧ (F x⁻¹ x ≡ e)

  Unique-Inverse : ∀ {n} {A : Set n} → (F : Binary-Operation A A A) → Identity F → Set n
  Unique-Inverse F record {witness = e} = ∀ {x} → ∃! x⁻¹ , (F x x⁻¹ ≡ e) ∧ (F x⁻¹ x ≡ e)

  Distributive : ∀ {n} {A : Set n} → (F : Binary-Operation A A A) → (G : Binary-Operation A A A) → Set n
  Distributive F G = ∀ {x y z} → ((G (F x y) z) ≡ (F (G x z) (G y z))) ∧ ((G z (F x y)) ≡ (F (G z x) (G z y)))

  Injection : ∀ {n} {S T : Set n} → (S → T) → Set n
  Injection φ = ∀ {x y z} → (φ x ≡ z) ∧ (φ y ≡ z) → x ≡ y

  Surjection : ∀ {n} {S T : Set n} → (S → T) → Set n
  Surjection φ = ∀ {y} → ∃ x , (φ x ≡ y)

  record Bijection {n} {S T : Set n} (F : S → T) : Set n where
    field
      injective : Injection F
      surjective : Surjection F
