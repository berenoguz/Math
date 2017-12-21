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
  infix 21 _==_
  infix 21 _≠_

  -- Disjunction
  data _∨_ : Set → Set → Set where
    ∨ᵢ₁ : ∀ {φ ψ} → φ → φ ∨ ψ -- Disjunction introduction
    ∨ᵢ₂ : ∀ {φ ψ} → ψ → φ ∨ ψ

  -- Logical Conjunction
  record _∧_ (φ ψ : Set) : Set where
    constructor ∧ᵢ
    field
      ∧ₑ₁_ : φ -- Conjunction elimination
      ∧ₑ₂ : ψ
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
    ● : φ == φ -- Equality is reflexive

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
      uniqueness : (x : S) → P x → x == witness
  syntax ∃! (λ x → e) = ∃! x , e

  -- Postulate Double Negation Elimination
  postulate ¬¬φ→φ : ∀ {φ} → ¬ ¬ φ → φ

  -- The Principle of Explosion (𝐸𝑥 𝐹𝑎𝑙𝑠𝑜 𝑄𝑢𝑜𝑑𝑙𝑖𝑏𝑒𝑡)
  postulate ⊥→φ : ∀ {φ : Set} → ⊥ → φ

  -- -- -- Theorems -- -- --

  -- The Principle of Non-Contradiction
  φ∧¬φ→⊥ : ∀ {φ : Set} → φ ∧ ¬ φ → ⊥
  φ∧¬φ→⊥ (∧ᵢ φ ¬φ) = ¬φ φ

  ¬φ∨ψ→φ→ψ : ∀ {φ ψ : Set} → ¬ φ ∨ ψ → φ → ψ
  ¬φ∨ψ→φ→ψ (∨ᵢ₁ ¬φ) = λ φ → ⊥→φ (φ∧¬φ→⊥ (∧ᵢ φ ¬φ))
  ¬φ∨ψ→φ→ψ (∨ᵢ₂ ψ) = λ φ → ψ

  -- Disjunction Elimination
  ∨ₑ : ∀ {φ ψ σ : Set} → φ ∨ ψ → (φ → σ) → (ψ → σ) → σ
  ∨ₑ (∨ᵢ₁ φ) φ→σ ψ→σ = φ→σ φ
  ∨ₑ (∨ᵢ₂ ψ) φ→σ ψ→σ = ψ→σ ψ

  ¬¬[φ∨¬φ] : ∀ {φ} → ¬ ¬ (φ ∨ ¬ φ)
  ¬¬[φ∨¬φ] = λ ¬[φ∨¬φ] → φ∧¬φ→⊥ (∧ᵢ (∨ᵢ₂ λ φ → lemma₁ ¬[φ∨¬φ] φ) ¬[φ∨¬φ])
    where
    lemma₁ : ∀ {φ} → ¬ (φ ∨ ¬ φ) → φ → ⊥
    lemma₁ ¬[φ∨¬φ] φ = φ∧¬φ→⊥ (∧ᵢ (∨ᵢ₁ φ) ¬[φ∨¬φ])

  -- The Principle of Excluded Middle (𝑇𝑒𝑟𝑡𝑖𝑖 𝐸𝑥𝑐𝑙𝑢𝑠𝑖)
  φ∨¬φ : ∀ {φ} → φ ∨ ¬ φ
  φ∨¬φ = ¬¬φ→φ ¬¬[φ∨¬φ]

  -- Reasoning Helpers

  -- Equality is symmetric
  ◆ : ∀ {n} {S : Set n} {φ ψ : S} → φ == ψ → ψ == φ
  ◆ ● = ●

  -- Equality is transitive
  ▲ : ∀ {n} {S : Set n} {φ ψ σ : S} → ψ == φ → φ == σ → ψ == σ
  ▲ ● ● = ●

  ▼ : ∀ {n} {S : Set n} {φ ψ σ : S} → (φ == ψ) → (σ == φ) → (ψ == σ)
  ▼ ● ● = ●

  -- Equality is right-euclidean
  ▶ : ∀ {n} {S : Set n} {φ ψ σ : S} → (φ == ψ) → (φ == σ) → (ψ == σ)
  ▶ ● ● = ●

  -- Equality is left-euclidean
  ◀ : ∀ {n} {S : Set n} {φ ψ σ : S} → (ψ == φ) → (σ == φ) → (ψ == σ)
  ◀ ● ● = ●

  -- Applying closed functions to equal arguments
  ■ : ∀ {n} {A B : Set n} {φ ψ : A} → (f : A → B) → φ == ψ → (f φ) == (f ψ)
  ■ f ● = ●
