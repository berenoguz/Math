-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of Natural Numbers
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

module Math.NaturalNumbers where
  open import Math.Logic using (_∨_; _∧_; ¬_; _≡_; _≠_; ∃)
  open import Agda.Builtin.Nat using (_+_) renaming
    (Nat to ℕ;
    suc to _′;
    _*_ to _·_) public

  infixl 19 _<_

  data _<_ (n : ℕ) : ℕ → Set where
    <-base : n < n ′
    <-ind : ∀ {m} → n < m → n < m ′

  _≤_ : ℕ → ℕ → Set
  x ≤ y = (x < y) ∨ (x ≡ y)

  _≥_ : ℕ → ℕ → Set
  x ≥ y = ¬ (x < y)

  _>_ : ℕ → ℕ → Set
  x > y = (x ≥ y) ∧ (x ≠ y)

  record ℕ⁺ : Set where
    field
      value : ℕ
      positive : 0 < value
