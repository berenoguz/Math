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
  open import Math.Logic using (¬_ ; _∨_ ; _≡_ ; _≠_)
  open import Agda.Primitive using (_⊔_; lzero; lsuc)

  -- Substitute
  subst : ∀ {n} {S : Set n} {x y : S} → (R : S → Set n) → R x → x ≡ y → R y
  subst _ Rx _≡_.reflexive-≡ = Rx

  Relation : ∀ {n} → Set n → Set ((lsuc lzero) ⊔ n)
  Relation S = S → S → Set

  Reflexive : ∀ {n} {S : Set n} → Relation S → Set n
  Reflexive R = ∀ {x} → R x x

  Irreflexive : ∀ {n} {S : Set n} → Relation S → Set n
  Irreflexive R = ∀ {x y} → R x y → x ≠ y

  Symmetric : ∀ {n} {S : Set n} → Relation S → Set n
  Symmetric R = ∀ {x y} → R x y → R y x

  Antisymmetric : ∀ {n} {S : Set n} → Relation S → Set n
  Antisymmetric R = ∀ {x y} → R x y → R y x → x ≡ y

  Asymmetric : ∀ {n} {S : Set n} → Relation S → Set n
  Asymmetric R = ∀ {x y} → R x y → ¬ (R y x)

  Transitive : ∀ {n} {S : Set n} → Relation S → Set n
  Transitive R = ∀ {x y z} → R x y → R y z → R x z

  Right-Euclidean : ∀ {n} {S : Set n} → Relation S → Set n
  Right-Euclidean R = ∀ {x y z} → R x y → R x z → R y z

  Left-Euclidean : ∀ {n} {S : Set n} → Relation S → Set n
  Left-Euclidean R = ∀ {x y z} → R y x → R z x → R y z

  Comparison : ∀ {n} {S : Set n} → Relation S → Set n
  Comparison R = ∀ {x y z} → R x z → R x y ∨ R y z

  Total : ∀ {n} {S : Set n} → Relation S → Set n
  Total R = ∀ {x y} → R x y ∨ R y x
