-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of Group Theory
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

module Math.Group where
  open import Math.Function
  open import Math.Logic using (∃ ; _∵_ ; _∧_ ; ∧-intro ; _==_ ; ∃! ; _∵_∵_ ; euclidean-==)
  open _∧_

  -- Definition of group
  -- Associative binary operation with an identity element and inverses.
  record Group {S : Set} (F : S → S → S) : Set where
    group-set = S
    group-operation = F
    field
      associative : Associative F
      identity : Identity F
      inverse : Inverse F identity
    identity-element = ∃.witness identity -- Identity Element
    inverse-of : (x : S) -- Map x ↦ ∃ x⁻¹
      → ∃ x⁻¹ , (F x x⁻¹ == identity-element) ∧ (F x⁻¹ x == identity-element)
    inverse-of x = inverse
  open Group

  -- Group identity is unique
  unique-identity : ∀ {S} {· : S → S → S} → Group · → Unique-Identity ·
  unique-identity 𝔊 = e ∵ identity-e ∵ unique-e
    where
    S = group-set 𝔊
    _·_ = group-operation 𝔊
    e = ∃.witness (identity 𝔊)
    identity-e = ∃.proof (identity 𝔊)
    unique-e : ∀ {e′ : S} → (∀ {x : S} → ((x · e′) == x) ∧ ((e′ · x) == x)) → e′ == e
    unique-e identity-e′ = euclidean-== (∧-elim₂ identity-e) (∧-elim₁ identity-e′)

  -- For each group element, its inverse is unique
  unique-inverse : ∀ {S} {· : S → S → S} → (G : Group ·)
    → (x : S) → Unique-Inverse · (identity G) x
  unique-inverse 𝔊 x = (x ⁻¹) ∵ (∃.proof ((inverse-of 𝔊) x)) ∵ uniqueness
    where
    S = group-set 𝔊
    _·_ = group-operation 𝔊
    e = ∃.witness (identity 𝔊)    
    _⁻¹ : S → S
    x ⁻¹ = ∃.witness ((inverse-of 𝔊) x)
    uniqueness : ∀ {inv : S} → ((x · inv) == e) ∧ ((inv · x) == e) → inv == (x ⁻¹)
    uniqueness = {!!}
