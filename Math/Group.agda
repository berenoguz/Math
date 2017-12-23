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
  open import Math.Logic using (∃ ; _∵_ ; _∧_ ; ∧-intro ; _==_ ; ∃! ; _∵_∵_ ; euclidean-== ; closure ; transitive-== ; symmetric-== ; left-euclidean-==)
  open _∧_

  -- Definition of group
  -- Associative binary operation with an identity element and inverses.
  record Group {A : Set} (F : A → A → A) : Set where
    S = A
    _·_ = F
    field
      associative : Associative F
      identity : Identity F
      inverse : Inverse F identity

    -- Reasoning Helper Theorems
    assoc₁◀ : ∀ {a b c d} → ((a · b) · c) == d → (a · (b · c)) == d
    assoc₁◀ eq = euclidean-== associative eq
    assoc₁▶ : ∀ {a b c d} → d == ((a · b) · c) → d == (a · (b · c))
    assoc₁▶ eq = transitive-== eq associative
    assoc₂◀ : ∀ {a b c d} → (a · (b · c)) == d → ((a · b) · c) == d
    assoc₂◀ eq = euclidean-== (symmetric-== associative) eq
    assoc₂▶ : ∀ {a b c d} → d == (a · (b · c)) → d == ((a · b) · c)
    assoc₂▶ eq = transitive-== eq (symmetric-== associative)

    e = ∃.witness identity -- Identity Element
    identity-e = ∃.proof identity -- Proof that e is the identity element
    identₑ₁◀ : ∀ {a b} → (a · e) == b → a == b
    identₑ₁◀ eq = euclidean-== (∧-elim₁ identity-e) eq
    identₑ₁▶ : ∀ {a b} → b == (a · e) → b == a
    identₑ₁▶ eq = transitive-== eq (∧-elim₁ identity-e) 
    identₑ₂◀ : ∀ {a b} → (e · a) == b → a == b
    identₑ₂◀ eq = euclidean-== (∧-elim₂ identity-e) eq
    identₑ₂▶ : ∀ {a b} → b == (e · a) → b == a
    identₑ₂▶ eq = transitive-== eq (∧-elim₂ identity-e)
    identᵢ₁◀ : ∀ {a b} → a == b → (a · e) == b
    identᵢ₁◀ eq = transitive-== (∧-elim₁ identity-e) eq
    identᵢ₁▶ : ∀ {a b} → a == b → a == (b · e)
    identᵢ₁▶ eq = transitive-== eq (symmetric-== (∧-elim₁ identity-e))
    identᵢ₂◀ : ∀ {a b} → a == b → (e · a) == b
    identᵢ₂◀ eq = transitive-== (∧-elim₂ identity-e) eq
    identᵢ₂▶ : ∀ {a b} → a == b → a == (e · b)
    identᵢ₂▶ eq = transitive-== eq (symmetric-== (∧-elim₂ identity-e))

    mul₁ : ∀ {a b c} → a == b → (a · c) == (b · c)
    mul₁ _==_.reflexive-== = _==_.reflexive-==
    mul₂ : ∀ {a b c} → a == b → (c · a) == (c · b)
    mul₂ _==_.reflexive-== = _==_.reflexive-==
    
    -- Identity Theorems
    unique-identity : Unique-Identity _·_ -- Group identity is unique
    unique-identity = e ∵ identity-e ∵ unique-e
      where
      unique-e : ∀ {e′} → (∀ {x : S} → ((x · e′) == x) ∧ ((e′ · x) == x)) → e′ == e
      unique-e identity-e′ = identₑ₂◀ (∧-elim₁ identity-e′)
    unique-e = ∃!.uniqueness unique-identity -- Proof that e is unique

    inverse-of : (x : S) -- Map x ↦ ∃ x⁻¹
      → ∃ x⁻¹ , (F x x⁻¹ == e) ∧ (F x⁻¹ x == e)
    inverse-of x = inverse
    infixl 22 _⁻¹
    _⁻¹ : S → S -- Inverse function. Map x ↦ x⁻¹
    x ⁻¹ = ∃.witness (inverse-of x)

    -- For each group element, its inverse is unique
    unique-inverse : Unique-Inverse _·_ identity
    unique-inverse = ∃.witness inverse ∵ ∃.proof inverse ∵ uniqueness
      where
      lemma : ∀ {x inv} → (x ⁻¹ · (x · inv)) == inv
      lemma = assoc₁◀ (identₑ₂▶ (mul₁ (∧-elim₂ (∃.proof inverse))))
      uniqueness : ∀ {x inv} → ((x · inv) == e) ∧ ((inv · x) == e) → inv == x ⁻¹
      uniqueness ass = symmetric-== (identₑ₁◀ (euclidean-== (mul₂ (∧-elim₁ ass)) lemma))

    -- Inverse of inverse of a is a
    a⁻¹⁻¹==a : (a : S) → a ⁻¹ ⁻¹ == a
    a⁻¹⁻¹==a a = left-euclidean-== (euclidean-== (lemma₂ (a ⁻¹ ⁻¹)) lemma₁) (symmetric-== (lemma₂ a))
      where
      lemma₁ : (a · (a ⁻¹ · a ⁻¹ ⁻¹)) == (a · (a ⁻¹ · a))
      lemma₁ = mul₂ (left-euclidean-== (∧-elim₁ (∃.proof inverse)) (∧-elim₂ (∃.proof inverse)))
      lemma₂ : (t : S) → (a · (a ⁻¹ · t)) == t
      lemma₂ t = euclidean-== associative (left-euclidean-== (closure (λ x → x · t) (∧-elim₁ (∃.proof inverse))) (symmetric-== (∧-elim₂ (∃.proof identity))))

    -- (a · b)⁻¹ = b⁻¹ · a⁻¹
    [a·b]⁻¹==b⁻¹·a⁻¹ : (a b : S) → (a · b) ⁻¹ == (b ⁻¹ · a ⁻¹)
    [a·b]⁻¹==b⁻¹·a⁻¹ a b = symmetric-== (left-euclidean-== (left-euclidean-== (closure (λ x → b ⁻¹ · x) lemma₂) associative) (euclidean-== (∧-elim₂ (∃.proof identity)) (closure (λ x → x · c) (symmetric-== (∧-elim₂ (∃.proof inverse))))))
      where
      c = (a · b) ⁻¹
      lemma₁ : a ⁻¹ == (a ⁻¹ · (a · (b · c)))
      lemma₁ = symmetric-== (left-euclidean-== (closure (λ x → a ⁻¹ · x) (euclidean-== associative (∧-elim₁ (∃.proof inverse)))) (symmetric-== (∧-elim₁ (∃.proof identity))))
      lemma₂ : a ⁻¹ == (b · c)
      lemma₂ = left-euclidean-== lemma₁ (euclidean-== (∧-elim₂ (∃.proof identity)) (left-euclidean-== (closure (λ x → x · (b · c)) (symmetric-== (∧-elim₂ (∃.proof inverse)))) (symmetric-== associative)))
