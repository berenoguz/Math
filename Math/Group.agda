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
  open import Math.Logic using (∃ ; _∵_ ; _∧_ ; ∧ᵢ ; _==_ ; ∃! ; _∵_∵_ ; ▶ ; ■ ; ◆ ; ◀)
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
    
    e = ∃.witness identity -- Identity Element
    identity-e = ∃.proof identity -- Proof that e is the identity element
    unique-identity : Unique-Identity _·_ -- Group identity is unique
    unique-identity = e ∵ identity-e ∵ unique-e
      where
      unique-e : (e′ : S) → (∀ {x : S} → ((x · e′) == x) ∧ ((e′ · x) == x)) → e′ == e
      unique-e e′ identity-e′ = ▶ (∧ₑ₂ identity-e) (∧ₑ₁ identity-e′)
    unique-e = ∃!.uniqueness unique-identity -- Proof that e is unique

    inverse-of : (x : S) -- Map x ↦ ∃ x⁻¹
      → ∃ x⁻¹ , (F x x⁻¹ == e) ∧ (F x⁻¹ x == e)
    inverse-of x = inverse
    infixl 22 _⁻¹
    _⁻¹ : S → S -- Inverse function. Map x ↦ x⁻¹
    x ⁻¹ = ∃.witness (inverse-of x)

    -- For each group element, its inverse is unique
    unique-inverse : (x : S) → Unique-Inverse _·_ identity x
    unique-inverse x = x⁻¹ ∵ ∃.proof (inverse-of x) ∵ uniqueness
      where
      x⁻¹ = x ⁻¹
      lemma₁ : ∀ {inv : S} → ((x · inv) == e) ∧ ((inv · x) == e)
        → (x⁻¹ · (x · inv)) == (x⁻¹ · e)
      lemma₁ inverse-inv = ■ (λ a → x⁻¹ · a) (∧ₑ₁ inverse-inv)
      lemma₂ : ∀ {inv : S} → ((x⁻¹ · x) · inv) == (x⁻¹ · (x · inv))
      lemma₂ = associative
      lemma₃ : (inv : S) → ((x⁻¹ · x) · inv) == (e · inv)
      lemma₃ inv = ■ (λ a → a · inv) (∧ₑ₂ (∃.proof (inverse-of x)))
      lemma₄ : (inv : S) → inv == (e · inv)
      lemma₄ inv = ◆ (∧ₑ₂ (∃.proof identity))
      lemma₅ : (inv : S) → (x⁻¹ · (x · inv)) == inv
      lemma₅ inv = ▶ lemma₂ (◀ (lemma₃ inv) (lemma₄ inv))
      lemma₆ : (x⁻¹ · e) == x⁻¹
      lemma₆ = ∧ₑ₁ (∃.proof identity)
      uniqueness : (inv : S) → ((x · inv) == e) ∧ ((inv · x) == e)
        → inv == x⁻¹
      uniqueness inv ass = ◆ (▶ lemma₆ (▶ (lemma₁ ass) (lemma₅ inv)))

    -- Inverse of inverse of a is a
    a⁻¹⁻¹==a : (a : S) → a ⁻¹ ⁻¹ == a
    a⁻¹⁻¹==a a = ◀ (▶ (lemma₂ (a ⁻¹ ⁻¹)) lemma₁) (◆ (lemma₂ a))
      where
      lemma₁ : (a · (a ⁻¹ · a ⁻¹ ⁻¹)) == (a · (a ⁻¹ · a))
      lemma₁ = ■ (λ x → a · x) (◀ (∧ₑ₁ (∃.proof inverse)) (∧ₑ₂ (∃.proof inverse)))
      lemma₂ : (t : S) → (a · (a ⁻¹ · t)) == t
      lemma₂ t = ▶ associative (◀ (■ (λ x → x · t) (∧ₑ₁ (∃.proof inverse))) (◆ (∧ₑ₂ (∃.proof identity))))

    -- (a · b)⁻¹ = b⁻¹ · a⁻¹
    [a·b]⁻¹==b⁻¹·a⁻¹ : (a b : S) → (a · b) ⁻¹ == (b ⁻¹ · a ⁻¹)
    [a·b]⁻¹==b⁻¹·a⁻¹ a b = ◆ (◀ (◀ (■ (λ x → b ⁻¹ · x) lemma₂) associative) (▶ (∧ₑ₂ (∃.proof identity)) (■ (λ x → x · c) (◆ (∧ₑ₂ (∃.proof inverse))))))
      where
      c = (a · b) ⁻¹
      lemma₁ : a ⁻¹ == (a ⁻¹ · (a · (b · c)))
      lemma₁ = ◆ (◀ (■ (λ x → a ⁻¹ · x) (▶ associative (∧ₑ₁ (∃.proof inverse)))) (◆ (∧ₑ₁ (∃.proof identity))))
      lemma₂ : a ⁻¹ == (b · c)
      lemma₂ = ◀ lemma₁ (▶ (∧ₑ₂ (∃.proof identity)) (◀ (■ (λ x → x · (b · c)) (◆ (∧ₑ₂ (∃.proof inverse)))) (◆ associative)))
