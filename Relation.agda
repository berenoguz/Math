-- Author : Beren Oguz <beren@berkeley.edu>
--
-- Formal definitions of various properties of relations
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
module Math.Relation where
  open import Math.Logic using (¬_ ; _∨_)
  open import Math.Equality using (_==_ ; _≠_)

  Relation : Set → Set₁
  Relation S = S → S → Set

  Reflexive : ∀ {S : Set} → Relation S → Set
  Reflexive R = ∀ {x} → R x x

  Irreflexive : ∀ {S : Set} → Relation S → Set
  Irreflexive R = ∀ {x y} → R x y → x ≠ y

  Symmetric : ∀ {S : Set} → Relation S → Set
  Symmetric R = ∀ {x y} → R x y → R y x

  Antisymmetric : ∀ {S : Set} → Relation S → Set
  Antisymmetric R = ∀ {x y} → R x y → R y x → x == y

  Asymmetric : ∀ {S : Set} → Relation S → Set
  Asymmetric R = ∀ {x y} → R x y → ¬ (R y x)

  Transitive : ∀ {S : Set} → Relation S → Set
  Transitive R = ∀ {x y z} → R x y → R y z → R x z

  Right-Euclidean : ∀ {S : Set} → Relation S → Set
  Right-Euclidean R = ∀ {x y z} → R x y → R x z → R y z

  Left-Euclidean : ∀ {S : Set} → Relation S → Set
  Left-Euclidean R = ∀ {x y z} → R y x → R z x → R y z

  Comparison : ∀ {S : Set} → Relation S → Set
  Comparison R = ∀ {x y z} → R x z → R x y ∨ R y z

  Total : ∀ {S : Set} → Relation S → Set
  Total R = ∀ {x y} → R x y ∨ R y x
