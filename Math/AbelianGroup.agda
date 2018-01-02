-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of Abelian Group Theory
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

module Math.AbelianGroup where
  open import Math.Group
  open import Math.Function
  open import Math.Logic
  import Math.Reasoning

  record Abelian-Group {ℓ} (A : Set ℓ) : Set ℓ where
    field
      group : Group A
      commutative : Commutative (Group._·_ group)
    open Group group hiding (_·_) public
    
    infixl 30 _+_
    _+_ = Group._·_ group

    open Math.Reasoning.Commutative _+_ commutative
