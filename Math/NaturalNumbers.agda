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
  open import Math.Logic using (_≠_ ; ∃)

  infixl 21 _′

  -- Definition of Natural Numbers
  data ℕ : Set where
    0̇ : ℕ -- 0 is in ℕ
    _′ : ℕ → ℕ -- For every natural, its successor is in ℕ
  1̇ = 0̇ ′
  2̇ = 1̇ ′
  3̇ = 2̇ ′

  -- Definition of natural addition
  _+_ : ℕ → ℕ → ℕ
  n + 0̇ = n
  n + m ′ = (n + m) ′

  _·_ : ℕ → ℕ → ℕ
  0̇ · 0̇ = 0̇
  n ′ · 0̇ = 0̇
  0̇ · m ′ = 0̇
  n ′ · m ′ = n ′ + (n · m ′)

  data _<_ (n : ℕ) : ℕ → Set where
    <-base : n < n ′
    <-ind : ∀ {m} → n < m → n < m ′

  record ℕ⁺ : Set where
    field
      value : ℕ
      positive : 0̇ < value
