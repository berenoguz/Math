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

module Math.Ring where
  open import Math.Logic
  open import Math.AbelianGroup
  open import Math.Group
  open import Math.Function

  -- Definition of Unitary Ring
  record Ring {ℓ} (S : Set ℓ) : Set ℓ where
    field
      abelian-group : Abelian-Group S
      _×_ : S → S → S
      associative : Associative _×_
      identity : Identity _×_      
      distributive : Distributive (Abelian-Group._+_ abelian-group) _×_
    open Abelian-Group abelian-group
      renaming (associative to group-associative;
               identity to group-identity;
               inverse to group-inverse;
               commutative to group-commutative;
               _⁻¹ to -_) public
    0̇ = ∃.witness group-identity
    1̇ = ∃.witness identity
    
