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
  ¬_ : Set → Set
  ¬ φ = φ → ⊥

  -- Biconditional
  _↔_ : Set → Set → Set
  φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)

  -- Existential quantification
  data ∃ {S : Set} (P : S → Set) : Set where
    _,_ : (x : S) → P x → ∃ P
  syntax ∃ (λ x → e) = ∃ x , e

  postulate ¬¬φ→φ : ∀ {φ} → ¬ ¬ φ → φ
  postulate ⊥→φ : ∀ {φ : Set} → ⊥ → φ

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

  φ∨¬φ : ∀ {φ} → φ ∨ ¬ φ
  φ∨¬φ = ¬¬φ→φ ¬¬[φ∨¬φ]
