-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of Ring Theory
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

module Math.CommutativeRing where
  open import Math.Logic
  open import Math.AbelianGroup
  open import Math.Group
  open import Math.Function
  open import Math.Ring
  open import Math.Reasoning

  -- Definition of Unitary Commutative Ring.
  -- This definition does not require a proof of Abelian Group
  -- since it can be proved from commutativity of ×
  record Commutative-Ring {ℓ} (S : Set ℓ) : Set ℓ where
    field
      group : Group S
      _×_ : S → S → S
      associative : Associative _×_
      identity : Identity _×_      
      distributive : Distributive (Group._·_ group) _×_
      commutative : Commutative _×_
    open Group group
      renaming (associative to group-associative;
               identity to group-identity;
               inverse to group-inverse;
               _·_ to _+_;
               _⁻¹ to -_) public
    0̇ = ∃.witness group-identity
    1̇ = ∃.witness identity

    open Math.Reasoning.Commutative _×_ commutative
      renaming (comm◀ to ʳcomm◀; comm▶ to ʳcomm▶; comm◆ to ʳcomm◆) public

    infixl 30 _×_

    -- group-commutative : Commutative _+_
    -- group-commutative = {!!}
    --   where
    --     lemma : ∀ {a b} → (1̇ + 1̇) × (a + b) ≡ ((a + b) + (a + b))
    --     lemma = {!!}
