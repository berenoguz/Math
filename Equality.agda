-- Author : Beren Oguz <beren@berkeley.edu>
--
-- Formalizes mathematical equality and some properties of it
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
module Math.Equality where
  open import Math.Logic using (¬_)

  infix 21 _==_
  infix 21 _≠_

  data _==_ {n} {S : Set n} (φ : S) : S → Set where
    reflexive-== : φ == φ
  
  symmetric-== : ∀ {n} {φ ψ : Set n} → φ == ψ → ψ == φ
  symmetric-== reflexive-== = reflexive-==

  transitive-== : ∀ {n} {φ ψ σ : Set n} → φ == ψ → ψ == σ → φ == σ
  transitive-== reflexive-== reflexive-== = reflexive-==

  euclidean-== : ∀ {n} {φ ψ σ : Set n} → φ == ψ → φ == σ → ψ == σ
  euclidean-== reflexive-== reflexive-== = reflexive-==

  left-euclidean-== : ∀ {n} {φ ψ σ : Set n} → ψ == φ → σ == φ → ψ == σ
  left-euclidean-== reflexive-== reflexive-== = reflexive-==

  _≠_ : ∀ {n} {S : Set n} → S → S → Set
  φ ≠ ψ = ¬ (φ == ψ)

  -- Uniqueness quantification
  record ∃! {n} {S : Set n} (P : S → Set) : Set n where
    constructor _,_,_
    field
      witness : S
      proof : P witness
      uniqueness : ∀ {x : S} → P x → x == witness
  syntax ∃! (λ x → e) = ∃! x , e
