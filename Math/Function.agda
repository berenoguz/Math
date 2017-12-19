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
  open import Math.Logic using (_∧_ ; ∃ ; _==_ ; ∃!)

  Binary-Operation : ∀ {n} → Set n → Set n → Set n → Set n
  Binary-Operation A B C = A → B → C

  Associative : ∀ {n} {A : Set n} → Binary-Operation A A A → Set n
  Associative F = ∀ {x y z} → F (F x y) z == F x (F y z)

  Commutative : ∀ {n} {A B : Set n} → Binary-Operation A A B → Set n
  Commutative F = ∀ {x y} → F x y == F y x

  Identity : ∀ {A : Set} → Binary-Operation A A A → Set
  Identity F = ∃ e , ∀ {x} → (F x e == x) ∧ (F e x == x)

  Unique-Identity : ∀ {A : Set} → Binary-Operation A A A → Set
  Unique-Identity F = ∃! e , ∀ {x} → (F x e == x) ∧ (F e x == x)

  Inverse : ∀ {A : Set} → (F : Binary-Operation A A A) → Identity F → Set
  Inverse F record {witness = e} = ∀ {x} → ∃ x⁻¹ , (F x x⁻¹ == e) ∧ (F x⁻¹ x == e)

  Unique-Inverse : ∀ {A : Set} → (F : Binary-Operation A A A) → Identity F → A → Set
  Unique-Inverse F record {witness = e} = λ x → ∃! x⁻¹ , (F x x⁻¹ == e) ∧ (F x⁻¹ x == e)
