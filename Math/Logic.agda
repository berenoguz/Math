-- Author : Beren Oguz <beren@berkeley.edu>
--
-- A formalization of First-Order Logic
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

module Math.Logic where

  -- -- -- Definitions -- -- --

  -- Operators
  infixr 24 ¬_
  infix 23 _∧_
  infix 23 _∨_
  infixr 22 ∃
  infix 21 _==_
  infix 21 _≠_

  -- Disjunction
  data _∨_ : Set → Set → Set where
    ∨-intro₁ : ∀ {φ ψ} → φ → φ ∨ ψ
    ∨-intro₂ : ∀ {φ ψ} → ψ → φ ∨ ψ

  -- Logical Conjunction
  record _∧_ (φ ψ : Set) : Set where
    constructor ∧-intro
    field
      ∧-elim₁ : φ
      ∧-elim₂ : ψ
  open _∧_

  -- True
  data ⊤ : Set where
    true : ⊤

  -- False
  data ⊥ : Set where

  -- Negation
  ¬_ : Set → Set -- ¬_ instead of ¬ makes parsing simpler
  ¬ φ = φ → ⊥

  -- Biconditional
  _↔_ : Set → Set → Set
  φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)

  -- Equality
  data _==_ {n} {S : Set n} (φ : S) : S → Set where
    reflexive-== : φ == φ -- Equality is reflexive

  -- Inequality
  _≠_ : ∀ {n} {S : Set n} → S → S → Set
  φ ≠ ψ = ¬ (φ == ψ)

  -- Existential quantification
  record ∃ {n} {S : Set n} (P : S → Set) : Set n where
    constructor _∵_
    claim = P
    field
      witness : S
      proof : P witness
  syntax ∃ (λ x → e) = ∃ x , e

  -- Uniqueness quantification
  record ∃! {n} {S : Set n} (P : S → Set) : Set n where
    constructor _∵_∵_
    claim = P
    field
      witness : S
      proof : P witness
      uniqueness : ∀ {x : S} → P x → x == witness
  syntax ∃! (λ x → e) = ∃! x , e

  -- Postulate Double Negation Elimination
  postulate ¬¬φ→φ : ∀ {φ} → ¬ ¬ φ → φ

  -- The Principle of Explosion (𝐸𝑥 𝐹𝑎𝑙𝑠𝑜 𝑄𝑢𝑜𝑑𝑙𝑖𝑏𝑒𝑡)
  postulate ⊥→φ : ∀ {φ : Set} → ⊥ → φ

  -- -- -- Theorems -- -- --

  -- The Principle of Non-Contradiction
  φ∧¬φ→⊥ : ∀ {φ : Set} → φ ∧ ¬ φ → ⊥
  φ∧¬φ→⊥ (∧-intro φ ¬φ) = ¬φ φ

  ¬φ∨ψ→φ→ψ : ∀ {φ ψ : Set} → ¬ φ ∨ ψ → φ → ψ
  ¬φ∨ψ→φ→ψ (∨-intro₁ ¬φ) = λ φ → ⊥→φ (φ∧¬φ→⊥ (∧-intro φ ¬φ))
  ¬φ∨ψ→φ→ψ (∨-intro₂ ψ) = λ φ → ψ

  ∨-elim : ∀ {φ ψ σ : Set} → φ ∨ ψ → (φ → σ) → (ψ → σ) → σ
  ∨-elim (∨-intro₁ φ) φ→σ ψ→σ = φ→σ φ
  ∨-elim (∨-intro₂ ψ) φ→σ ψ→σ = ψ→σ ψ

  ¬¬[φ∨¬φ] : ∀ {φ} → ¬ ¬ (φ ∨ ¬ φ)
  ¬¬[φ∨¬φ] = λ ¬[φ∨¬φ] → φ∧¬φ→⊥ (∧-intro (∨-intro₂ λ φ → lemma₁ ¬[φ∨¬φ] φ) ¬[φ∨¬φ])
    where
    lemma₁ : ∀ {φ} → ¬ (φ ∨ ¬ φ) → φ → ⊥
    lemma₁ ¬[φ∨¬φ] φ = φ∧¬φ→⊥ (∧-intro (∨-intro₁ φ) ¬[φ∨¬φ])

  -- The Principle of Excluded Middle (𝑇𝑒𝑟𝑡𝑖𝑖 𝐸𝑥𝑐𝑙𝑢𝑠𝑖)
  φ∨¬φ : ∀ {φ} → φ ∨ ¬ φ
  φ∨¬φ = ¬¬φ→φ ¬¬[φ∨¬φ]

  -- Equality is symmetric
  symmetric-== : ∀ {n} {S : Set n} {φ ψ : S} → φ == ψ → ψ == φ
  symmetric-== reflexive-== = reflexive-==

  -- Equality is transitive
  transitive-== : ∀ {n} {S : Set n} {φ ψ σ : S} → φ == ψ → ψ == σ → φ == σ
  transitive-== reflexive-== reflexive-== = reflexive-==

  -- Equality is right euclidean
  euclidean-== : ∀ {n} {S : Set n} {φ ψ σ : S} → (φ == ψ) → (φ == σ) → (ψ == σ)
  euclidean-== reflexive-== reflexive-== = reflexive-==

  -- Equality is left euclidean
  left-euclidean-== : ∀ {n} {S : Set n} {φ ψ σ : S} → ψ == φ → σ == φ → ψ == σ
  left-euclidean-== reflexive-== reflexive-== = reflexive-==

  -- Applying closed functions to equal arguments
  closure : ∀ {n} {A B : Set n} {φ ψ : A} → (f : A → B) → φ == ψ → (f φ) == (f ψ)
  closure f reflexive-== = reflexive-==

  postulate left-closure : ∀ {n} {S : Set n} {φ ψ σ : S} → (_·_ : S → S → S) → φ == ψ → (σ · φ) == (σ · ψ)

  postulate right-closure : ∀ {n} {S : Set n} {φ ψ σ : S} → (_·_ : S → S → S) → φ == ψ → (φ · σ) == (ψ · σ)
