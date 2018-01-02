-- Author : Beren Oguz <beren@berkeley.edu>
--
-- Reasoning Helper functions
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

module Math.Reasoning where
  open import Math.Logic
  open import Math.Function

  open ∃
  open _∧_

  module Associative {ℓ} {S : Set ℓ} (_·_ : S → S → S) (associative : Associative _·_) where
    assoc₁◀ : ∀ {a b c d} → ((a · b) · c) ≡ d → (a · (b · c)) ≡ d
    assoc₁◀ eq = euclidean-≡ associative eq
    assoc₁▶ : ∀ {a b c d} → d ≡ ((a · b) · c) → d ≡ (a · (b · c))
    assoc₁▶ eq = transitive-≡ eq associative
    assoc₂◀ : ∀ {a b c d} → (a · (b · c)) ≡ d → ((a · b) · c) ≡ d
    assoc₂◀ eq = euclidean-≡ (symmetric-≡ associative) eq
    assoc₂▶ : ∀ {a b c d} → d ≡ (a · (b · c)) → d ≡ ((a · b) · c)
    assoc₂▶ eq = transitive-≡ eq (symmetric-≡ associative)
    assoc₁◆ : ∀ {a b c f g h}
      → ((a · b) · c) ≡ ((f · g) · h) → (a · (b · c)) ≡ (f · (g · h))
    assoc₁◆ eq = assoc₁◀ (assoc₁▶ eq)
    assoc₂◆ : ∀ {a b c f g h}
      → (a · (b · c)) ≡ (f · (g · h)) → ((a · b) · c) ≡ ((f · g) · h)
    assoc₂◆ eq = assoc₂◀ (assoc₂▶ eq)

  module Commutative {ℓ} {S : Set ℓ} (_·_ : S → S → S) (commutative : Commutative _·_) where
    comm◀ : ∀ {a b d} → (a · b) ≡ d → (b · a) ≡ d
    comm◀ eq = transitive-≡ commutative eq
    comm▶ : ∀ {a b d} → d ≡ (a · b) → d ≡ (b · a)
    comm▶ eq = symmetric-≡ ∘ comm◀ ∘ symmetric-≡ ← eq
    comm◆ : ∀ {a b c d} → (a · b) ≡ (c · d) → (b · a) ≡ (d · c)
    comm◆ eq = comm◀ ∘ comm▶ ← eq

  module Identity {ℓ} {S : Set ℓ} (_·_ : S → S → S) (identity : Identity _·_) where
    e = witness identity
    identity-e = proof identity
    identₑ₁◀ : ∀ {a b} → (a · e) ≡ b → a ≡ b
    identₑ₁◀ eq = euclidean-≡ (∧ₑᵣ identity-e) eq
    identₑ₁▶ : ∀ {a b} → b ≡ (a · e) → b ≡ a
    identₑ₁▶ eq = transitive-≡ eq (∧ₑᵣ identity-e) 
    identₑ₂◀ : ∀ {a b} → (e · a) ≡ b → a ≡ b
    identₑ₂◀ eq = euclidean-≡ (∧ₑₗ identity-e) eq
    identₑ₂▶ : ∀ {a b} → b ≡ (e · a) → b ≡ a
    identₑ₂▶ eq = transitive-≡ eq (∧ₑₗ identity-e)
    identᵢ₁◀ : ∀ {a b} → a ≡ b → (a · e) ≡ b
    identᵢ₁◀ eq = transitive-≡ (∧ₑᵣ identity-e) eq
    identᵢ₁▶ : ∀ {a b} → a ≡ b → a ≡ (b · e)
    identᵢ₁▶ eq = transitive-≡ eq (symmetric-≡ (∧ₑᵣ identity-e))
    identᵢ₂◀ : ∀ {a b} → a ≡ b → (e · a) ≡ b
    identᵢ₂◀ eq = transitive-≡ (∧ₑₗ identity-e) eq
    identᵢ₂▶ : ∀ {a b} → a ≡ b → a ≡ (e · b)
    identᵢ₂▶ eq = transitive-≡ eq (symmetric-≡ (∧ₑₗ identity-e))

  module Binary-Operation {ℓ} {S : Set ℓ} (_·_ : S → S → S) where
    mul₁ : ∀ {a b c} → a ≡ b → (a · c) ≡ (b · c)
    mul₁ _≡_.reflexive-≡ = _≡_.reflexive-≡
    mul₂ : ∀ {a b c} → a ≡ b → (c · a) ≡ (c · b)
    mul₂ _≡_.reflexive-≡ = _≡_.reflexive-≡

  module Inverse {ℓ} {S : Set ℓ} (_·_ : S → S → S) (identity : Identity _·_)
    (inverse : Inverse _·_ identity) where
    open Identity _·_ identity
    open Binary-Operation _·_

    inverse-of : (x : S) -- Map x ↦ ∃ x⁻¹
      → ∃ x⁻¹ , ((x · x⁻¹) ≡ e) ∧ ((x⁻¹ · x) ≡ e)
    inverse-of x = inverse
    infixl 22 _⁻¹
    _⁻¹ : S → S -- Inverse function. Map x ↦ x⁻¹
    x ⁻¹ = ∃.witness (inverse-of x)

    invₑ₁₁◀ : ∀ {a b c}
      → ((a · a ⁻¹) · b) ≡ c → b ≡ c
    invₑ₁₁◀ eq = euclidean-≡ ((identₑ₂▶ ∘ mul₁ ∘ ∧ₑᵣ) (∃.proof inverse)) eq
    invₑ₁₁▶ : ∀ {a b c}
      → c ≡ ((a · a ⁻¹) · b) → c ≡ b
    invₑ₁₁▶ eq = (symmetric-≡ ∘ invₑ₁₁◀ ∘ symmetric-≡) eq
    invₑ₂₁◀ : ∀ {a b c}
      → ((a ⁻¹ · a) · b) ≡ c → b ≡ c
    invₑ₂₁◀ eq = euclidean-≡ (identₑ₂▶ (mul₁ (∧ₑₗ (∃.proof inverse)))) eq
    invₑ₂₁▶ : ∀ {a b c}
      → c ≡ ((a ⁻¹ · a) · b) → c ≡ b
    invₑ₂₁▶ eq = symmetric-≡ (invₑ₂₁◀ (symmetric-≡ eq))
    invₑ₁₁◆ : ∀ {a b f g}
      → ((a · a ⁻¹) · b) ≡ ((f · f ⁻¹) · g) → b ≡ g
    invₑ₁₁◆ eq = invₑ₁₁▶ (invₑ₁₁◀ eq)
    invₑ₂₁◆ : ∀ {a b f g}
      → ((a ⁻¹ · a) · b) ≡ ((f ⁻¹ · f) · g) → b ≡ g
    invₑ₂₁◆ eq = invₑ₂₁▶ (invₑ₂₁◀ eq)
    invₑ₁₂◀ : ∀ {a b c}
      → (b · (a · a ⁻¹)) ≡ c → b ≡ c
    invₑ₁₂◀ eq = euclidean-≡ (identₑ₁▶ (mul₂ (∧ₑᵣ (∃.proof inverse)))) eq
    invₑ₁₂▶ : ∀ {a b c}
      → c ≡ (b · (a · a ⁻¹)) → c ≡ b
    invₑ₁₂▶ eq = symmetric-≡ (invₑ₁₂◀ (symmetric-≡ eq))
    invₑ₂₂◀ : ∀ {a b c}
      → (b · (a ⁻¹ · a)) ≡ c → b ≡ c
    invₑ₂₂◀ eq = euclidean-≡ (identₑ₁▶ (mul₂ (∧ₑₗ (∃.proof inverse)))) eq
    invₑ₂₂▶ : ∀ {a b c}
      → c ≡ (b · (a ⁻¹ · a)) → c ≡ b
    invₑ₂₂▶ eq = symmetric-≡ (invₑ₂₂◀ (symmetric-≡ eq))
    invₑ₁₂◆ : ∀ {a b f g}
      → (b · (a · a ⁻¹) ) ≡ (g · (f · f ⁻¹)) → b ≡ g
    invₑ₁₂◆ eq = invₑ₁₂▶ (invₑ₁₂◀ eq)
    invₑ₂₂◆ : ∀ {a b f g}
      → (b · (a ⁻¹ · a)) ≡ (g · (f ⁻¹ · f)) → b ≡ g
    invₑ₂₂◆ eq = invₑ₂₂▶ (invₑ₂₂◀ eq)

