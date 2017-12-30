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
  infixr 25 ¬_
  infix 24 _∧_
  infix 24 _∨_
  infixr 23 ∃
  infix 21 _≡_
  infix 21 _≠_

  -- Disjunction
  data _∨_ {n} : Set n → Set n → Set n where
    ∨ᵢᵣ : ∀ {φ ψ} → φ → φ ∨ ψ -- Introduce (∨ ψ)
    ∨ᵢₗ : ∀ {φ ψ} → ψ → φ ∨ ψ -- Introduce (ψ ∨)

  -- Logical Conjunction
  record _∧_ {n} (φ ψ : Set n) : Set n where
    constructor ∧ᵢ
    field
      ∧ₑᵣ : φ -- Eliminate (∧ ψ)
      ∧ₑₗ : ψ -- Eliminate (ψ ∧)
  open _∧_

  -- True
  data ⊤ : Set where
    true : ⊤

  -- False
  data ⊥ : Set where

  -- -- Negation
  ¬_ : ∀ {n} → Set n → Set n -- ¬_ instead of ¬ makes parsing simpler
  ¬ φ = φ → ⊥

  -- -- Biconditional
  _↔_ : ∀ {n} → Set n → Set n → Set n
  φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)

  -- -- Equality
  data _≡_ {n} {S : Set n} (φ : S) : S → Set where
    reflexive-≡ : φ ≡ φ -- Equality is reflexive

  -- -- Inequality
  _≠_ : ∀ {n} {S : Set n} → S → S → Set
  φ ≠ ψ = ¬ (φ ≡ ψ)

  -- -- Existential quantification
  record ∃ {n} {S : Set n} (P : S → Set) : Set n where
    constructor _∵_
    claim = P
    field
      witness : S
      proof : P witness
  syntax ∃ (λ x → e) = ∃ x , e

  -- -- Uniqueness quantification
  record ∃! {n} {S : Set n} (P : S → Set) : Set n where
    constructor _∵_∵_
    claim = P
    field
      witness : S
      proof : P witness
      uniqueness : ∀ {x} → P x → x ≡ witness
  syntax ∃! (λ x → e) = ∃! x , e

  -- -- -- Theorems -- -- --

  -- The Principle of Explosion (𝐸𝑥 𝐹𝑎𝑙𝑠𝑜 𝑄𝑢𝑜𝑑𝑙𝑖𝑏𝑒𝑡)
  ⊥→φ : ∀ {n} {φ : Set n} → ⊥ → φ
  ⊥→φ ()

  -- The Principle of Non-Contradiction
  φ∧¬φ→⊥ : ∀ {n} {φ : Set n} → φ ∧ ¬ φ → ⊥
  φ∧¬φ→⊥ (∧ᵢ φ ¬φ) = ¬φ φ

  ¬φ∨ψ→φ→ψ : ∀ {φ ψ : Set} → ¬ φ ∨ ψ → φ → ψ
  ¬φ∨ψ→φ→ψ (∨ᵢᵣ ¬φ) = λ φ → ⊥→φ (φ∧¬φ→⊥ (∧ᵢ φ ¬φ))
  ¬φ∨ψ→φ→ψ (∨ᵢₗ ψ) = λ φ → ψ

  ∨-elim : ∀ {φ ψ σ : Set} → φ ∨ ψ → (φ → σ) → (ψ → σ) → σ
  ∨-elim (∨ᵢᵣ φ) φ→σ ψ→σ = φ→σ φ
  ∨-elim (∨ᵢₗ ψ) φ→σ ψ→σ = ψ→σ ψ

  ¬¬[φ∨¬φ] : ∀ {n} {φ : Set n} → ¬ ¬ (φ ∨ ¬ φ)
  ¬¬[φ∨¬φ] = λ ¬[φ∨¬φ] → φ∧¬φ→⊥ (∧ᵢ (∨ᵢₗ λ φ → lemma₁ ¬[φ∨¬φ] φ) ¬[φ∨¬φ])
    where
    lemma₁ : ∀ {φ} → ¬ (φ ∨ ¬ φ) → φ → ⊥
    lemma₁ ¬[φ∨¬φ] φ = φ∧¬φ→⊥ (∧ᵢ (∨ᵢᵣ φ) ¬[φ∨¬φ])

  -- Equality is symmetric
  symmetric-≡ : ∀ {n} {S : Set n} {φ ψ : S} → φ ≡ ψ → ψ ≡ φ
  symmetric-≡ reflexive-≡ = reflexive-≡

  -- Equality is transitive
  transitive-≡ : ∀ {n} {S : Set n} {φ ψ σ : S} → φ ≡ ψ → ψ ≡ σ → φ ≡ σ
  transitive-≡ reflexive-≡ reflexive-≡ = reflexive-≡

  -- Equality is right euclidean
  euclidean-≡ : ∀ {n} {S : Set n} {φ ψ σ : S} → (φ ≡ ψ) → (φ ≡ σ) → (ψ ≡ σ)
  euclidean-≡ reflexive-≡ reflexive-≡ = reflexive-≡

  -- Equality is left euclidean
  left-euclidean-≡ : ∀ {n} {S : Set n} {φ ψ σ : S} → (ψ ≡ φ) → (σ ≡ φ) → (ψ ≡ σ)
  left-euclidean-≡ reflexive-≡ reflexive-≡ = reflexive-≡

  -- Applying closed functions to equal arguments
  closure : ∀ {n} {A B : Set n} {φ ψ : A} → (f : A → B) → φ ≡ ψ → (f φ) ≡ (f ψ)
  closure f reflexive-≡ = reflexive-≡

  -- Classical-Logic. Assumes double negation elimination
  module Classical-Logic (¬¬φ→φ : ∀ {n} {φ : Set n} → ¬ ¬ φ → φ) where
    -- The Principle of Excluded Middle (𝑇𝑒𝑟𝑡𝑖𝑖 𝐸𝑥𝑐𝑙𝑢𝑠𝑖)
    φ∨¬φ : ∀ {n} {φ : Set n} → φ ∨ ¬ φ
    φ∨¬φ = ¬¬φ→φ ¬¬[φ∨¬φ]
