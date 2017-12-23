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
  open import Math.Logic using (∃ ; _∵_ ; _∧_ ; ∧-intro ; _==_ ; ∃! ; _∵_∵_ ; euclidean-== ; closure ; transitive-== ; symmetric-== ; left-euclidean-== ; ¬_ ; _≠_)
  open _∧_
  open import Math.NaturalNumbers using (ℕ ; _<_ ; 0̇ ; _′ ; ℕ⁺)

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
    assoc₁◆ : ∀ {a b c f g h}
      → ((a · b) · c) == ((f · g) · h) → (a · (b · c)) == (f · (g · h))
    assoc₁◆ eq = assoc₁◀ (assoc₁▶ eq)
    assoc₂◆ : ∀ {a b c f g h}
      → (a · (b · c)) == (f · (g · h)) → ((a · b) · c) == ((f · g) · h)
    assoc₂◆ eq = assoc₂◀ (assoc₂▶ eq)
    
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

    -- Inverse Theorems
    a⁻¹·a⁻¹⁻¹==a·a⁻¹ : ∀ {a} → (a ⁻¹ · a ⁻¹ ⁻¹) == (a ⁻¹ · a)
    a⁻¹·a⁻¹⁻¹==a·a⁻¹ = left-euclidean-== (∧-elim₁ (∃.proof inverse)) (∧-elim₂ (∃.proof inverse))

    a·a⁻¹==a⁻¹·a⁻¹⁻¹ : ∀ {a} → (a ⁻¹ · a) == (a ⁻¹ · a ⁻¹ ⁻¹)
    a·a⁻¹==a⁻¹·a⁻¹⁻¹ = symmetric-== a⁻¹·a⁻¹⁻¹==a·a⁻¹

    invₑ₁₁◀ : ∀ {a b c}
      → ((a · a ⁻¹) · b) == c → b == c
    invₑ₁₁◀ eq = euclidean-== (identₑ₂▶ (mul₁ (∧-elim₁ (∃.proof inverse)))) eq
    invₑ₁₁▶ : ∀ {a b c}
      → c == ((a · a ⁻¹) · b) → c == b
    invₑ₁₁▶ eq = symmetric-== (invₑ₁₁◀ (symmetric-== eq))
    invₑ₂₁◀ : ∀ {a b c}
      → ((a ⁻¹ · a) · b) == c → b == c
    invₑ₂₁◀ eq = euclidean-== (identₑ₂▶ (mul₁ (∧-elim₂ (∃.proof inverse)))) eq
    invₑ₂₁▶ : ∀ {a b c}
      → c == ((a ⁻¹ · a) · b) → c == b
    invₑ₂₁▶ eq = symmetric-== (invₑ₂₁◀ (symmetric-== eq))
    invₑ₁₁◆ : ∀ {a b f g}
      → ((a · a ⁻¹) · b) == ((f · f ⁻¹) · g) → b == g
    invₑ₁₁◆ eq = invₑ₁₁▶ (invₑ₁₁◀ eq)
    invₑ₂₁◆ : ∀ {a b f g}
      → ((a ⁻¹ · a) · b) == ((f ⁻¹ · f) · g) → b == g
    invₑ₂₁◆ eq = invₑ₂₁▶ (invₑ₂₁◀ eq)
    invₑ₁₂◀ : ∀ {a b c}
      → (b · (a · a ⁻¹)) == c → b == c
    invₑ₁₂◀ eq = euclidean-== (identₑ₁▶ (mul₂ (∧-elim₁ (∃.proof inverse)))) eq
    invₑ₁₂▶ : ∀ {a b c}
      → c == (b · (a · a ⁻¹)) → c == b
    invₑ₁₂▶ eq = symmetric-== (invₑ₁₂◀ (symmetric-== eq))
    invₑ₂₂◀ : ∀ {a b c}
      → (b · (a ⁻¹ · a)) == c → b == c
    invₑ₂₂◀ eq = euclidean-== (identₑ₁▶ (mul₂ (∧-elim₂ (∃.proof inverse)))) eq
    invₑ₂₂▶ : ∀ {a b c}
      → c == (b · (a ⁻¹ · a)) → c == b
    invₑ₂₂▶ eq = symmetric-== (invₑ₂₂◀ (symmetric-== eq))
    invₑ₁₂◆ : ∀ {a b f g}
      → (b · (a · a ⁻¹) ) == (g · (f · f ⁻¹)) → b == g
    invₑ₁₂◆ eq = invₑ₁₂▶ (invₑ₁₂◀ eq)
    invₑ₂₂◆ : ∀ {a b f g}
      → (b · (a ⁻¹ · a)) == (g · (f ⁻¹ · f)) → b == g
    invₑ₂₂◆ eq = invₑ₂₂▶ (invₑ₂₂◀ eq)
  
    -- For each group element, its inverse is unique
    unique-inverse : Unique-Inverse _·_ identity
    unique-inverse = ∃.witness inverse ∵ ∃.proof inverse ∵ uniqueness
      where
        lemma : ∀ {x inv} → (x ⁻¹ · (x · inv)) == inv
        lemma = assoc₁◀ (identₑ₂▶ (mul₁ (∧-elim₂ (∃.proof inverse))))
        uniqueness : ∀ {x inv} → ((x · inv) == e) ∧ ((inv · x) == e) → inv == x ⁻¹
        uniqueness ass = symmetric-== (identₑ₁◀ (euclidean-== (mul₂ (∧-elim₁ ass)) lemma))
  
    -- Inverse of inverse of a is a
    a⁻¹⁻¹==a : ∀ {a} → a ⁻¹ ⁻¹ == a
    a⁻¹⁻¹==a = left-euclidean-== (euclidean-== lemma (mul₂ a⁻¹·a⁻¹⁻¹==a·a⁻¹)) (symmetric-== lemma)
      where
        lemma : ∀ {a t} → (a · (a ⁻¹ · t)) == t
        lemma = assoc₁◀ (left-euclidean-== (mul₁ (∧-elim₁ (∃.proof inverse))) (symmetric-== (∧-elim₂ (∃.proof identity))))

    [a·b]⁻¹==b⁻¹·a⁻¹ : ∀ a b → (a · b) ⁻¹ == (b ⁻¹ · a ⁻¹)
    [a·b]⁻¹==b⁻¹·a⁻¹ a b = symmetric-== (left-euclidean-== (left-euclidean-== (closure (λ x → b ⁻¹ · x) lemma₂) associative) (euclidean-== (∧-elim₂ (∃.proof identity)) (closure (λ x → x · c) (symmetric-== (∧-elim₂ (∃.proof inverse))))))
      where
        c = (a · b) ⁻¹
        lemma₁ : a ⁻¹ == (a ⁻¹ · (a · (b · c)))
        lemma₁ = symmetric-== (left-euclidean-== (closure (λ x → a ⁻¹ · x) (euclidean-== associative (∧-elim₁ (∃.proof inverse)))) (symmetric-== (∧-elim₁ (∃.proof identity))))
        lemma₂ : a ⁻¹ == (b · c)
        lemma₂ = left-euclidean-== lemma₁ (euclidean-== (∧-elim₂ (∃.proof identity)) (left-euclidean-== (closure (λ x → x · (b · c)) (symmetric-== (∧-elim₂ (∃.proof inverse)))) (symmetric-== associative)))

    -- Cancellation Laws
    cancel₁ : ∀ {a b c} → (a · b) == (a · c) → b == c
    cancel₁ eq = invₑ₂₁◆ (assoc₂◆ (mul₂ eq))
    cancel₂ : ∀ {a b c} → (b · a) == (c · a) → b == c
    cancel₂ eq = invₑ₁₂◆ (assoc₁◆ (mul₁ eq))

    -- Exponentive Notation

    _^_ : S → ℕ → S
    a ^ 0̇ = e
    a ^ n ′ = a · (a ^ n)

    -- Order
    record order (x : S) (n-proof : ℕ⁺) : Set where
      n = ℕ⁺.value n-proof
      field
        prop₁ : (x ^ n) == e
        minimum : ∀ {m} → (ℕ⁺.value m) < n → (x ^ n) ≠ e
        
      
