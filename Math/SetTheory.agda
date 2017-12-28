-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of Set Theory
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

module Math.SetTheory where
  open import Math.Logic
  open import Agda.Primitive using (lsuc)

  record Subset {n} (S : Set n) : Set (lsuc n) where
    field
      R : S → Set

  data includes {n} (S : Set n) : S → Set where
    x:S→x∈S : ∀ {x : S} → includes S x 

  syntax includes x S = x ∈ S
