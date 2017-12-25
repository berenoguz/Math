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
  open import Math.Relation using (subst)
  open import Math.Function
  open import Math.Logic using (∃ ; _∵_ ; _∧_ ; ∧-intro ; _==_ ; ∃! ; _∵_∵_ ; euclidean-== ; closure ; transitive-== ; symmetric-== ; left-euclidean-== ; ¬_ ; _≠_ ; _∨_)
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

    -- A relation relating to all members of S
    data _∈S (x : S) : Set where
      all : x ∈S

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
    invₑ₁₁◀ eq = euclidean-== ((identₑ₂▶ ∘ mul₁ ∘ ∧-elim₁) (∃.proof inverse)) eq
    invₑ₁₁▶ : ∀ {a b c}
      → c == ((a · a ⁻¹) · b) → c == b
    invₑ₁₁▶ eq = (symmetric-== ∘ invₑ₁₁◀ ∘ symmetric-==) eq
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

    [a·b]⁻¹==b⁻¹·a⁻¹ : ∀ {a b} → (a · b) ⁻¹ == (b ⁻¹ · a ⁻¹)
    [a·b]⁻¹==b⁻¹·a⁻¹ = symmetric-== (left-euclidean-== (left-euclidean-== (mul₂ lemma₂) associative) (euclidean-== (∧-elim₂ (∃.proof identity)) (mul₁ (symmetric-== (∧-elim₂ (∃.proof inverse))))))
      where
        lemma₁ : ∀ {a b} → a ⁻¹ == (a ⁻¹ · (a · (b · ((a · b) ⁻¹))))
        lemma₁ = symmetric-== (left-euclidean-== (mul₂ (euclidean-== associative (∧-elim₁ (∃.proof inverse)))) (symmetric-== (∧-elim₁ (∃.proof identity))))
        lemma₂ : ∀ {a b} → a ⁻¹ == (b · ((a · b) ⁻¹))
        lemma₂ = left-euclidean-== lemma₁ (euclidean-== (∧-elim₂ (∃.proof identity)) (left-euclidean-== (mul₁ (symmetric-== (∧-elim₂ (∃.proof inverse)))) (symmetric-== associative)))
    b⁻¹·a⁻¹==[a·b]⁻¹ : ∀ {a b} → (b ⁻¹ · a ⁻¹) == (a · b) ⁻¹
    b⁻¹·a⁻¹==[a·b]⁻¹ = symmetric-== [a·b]⁻¹==b⁻¹·a⁻¹

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
  
  -- Group Homomorphism
  record Homomorphism {S T} {_★_ : S → S → S} {_◇_ : T → T → T}
    (G : Group _★_) (H : Group _◇_) (f : S → T) : Set where
      φ = f
      field
        homomorphism : ∀ {x y} → φ (x ★ y) == (φ x ◇ φ y)
      kernel : S → Set
      kernel g = φ g == (Group.e H)

  -- Group Isomorphism
  record Isomorphism {S T} {_★_ : S → S → S} {_◇_ : T → T → T}
    (G : Group _★_) (H : Group _◇_) (f : S → T) : Set where
      φ = f    
      field
        homomorphism-proof : Homomorphism G H φ
        bijection : Bijection φ
      homomorphism = Homomorphism.homomorphism homomorphism-proof

  record Action {V} {F : V → V → V} (G : Group F) (A : Set) (f : V → A → A) : Set where
    open Group G
    φ = f
    field
      prop₁ : ∀ {x y a} → φ x (φ y a) == φ (x · y) a
      prop₂ : ∀ {a} → φ e a == a
    kernel : S → Set
    kernel g = ∀ {s} → φ g s == s

  record Subgroup {S} {F : S → S → S} (G : Group F) (R : S → Set) : Set where
    open Group G
    field
      nonempty : R e
      closed-· : ∀ {x y} → R x ∧ R y → R (x · y)
      closed-⁻¹ : ∀ {x} → R x → R (x ⁻¹)

  -- Subgroup Criterion
  subgroup-criterion : ∀ {S} {F : S → S → S} → (G : Group F) → (R : S → Set)
    → ∃ z , R z → (∀ {x y} → R x ∧ R y → R ((Group._·_ G) x ((Group._⁻¹ G) y)))
    → Subgroup G R
  subgroup-criterion G R ∃Rz ass = record {
                     nonempty = Re ;
                     closed-· = closed-·-proof ;
                     closed-⁻¹ = closed-⁻¹-proof
                     }
    where
    open Group G
    z = ∃.witness ∃Rz
    Rz = ∃.proof ∃Rz
    Re : R e
    Re = subst R (ass (∧-intro Rz Rz)) (∧-elim₁ (∃.proof inverse))
    closed-⁻¹-proof : ∀ {x} → R x →  R (x ⁻¹)
    closed-⁻¹-proof Rx = subst R (ass (∧-intro Re Rx)) (identₑ₂▶ _==_.reflexive-==)
    lemma : ∀ {x y} → R (y ⁻¹ · x ⁻¹) → R (x · y)
    lemma Ry⁻¹·x⁻¹ = subst R (closed-⁻¹-proof (subst R Ry⁻¹·x⁻¹ b⁻¹·a⁻¹==[a·b]⁻¹)) a⁻¹⁻¹==a
    closed-·-proof : ∀ {x y} → R x ∧ R y → R (x · y)
    closed-·-proof (∧-intro Rx Ry) = lemma (ass (∧-intro (closed-⁻¹-proof Ry) Rx))

  Centralizer : ∀ {S} {F : S → S → S} (G : Group F) (A : S → Set) → ∃ z , (A z) → S → Set
  Centralizer G A ∃Az g = ∀ {a} → A a → (g · a) == (a · g) where open Group G

  -- Alternative definition of centralizer
  alternative-centralizer : ∀ {S} {_·_ : S → S → S} {g a} → (G : Group _·_) → (g · (a · ((Group._⁻¹ G) g))) == a → (g · a) == (a · g)
  alternative-centralizer G ass = euclidean-== (mul₂ ∘ invₑ₂₂▶ ← associative) (assoc₁◀ ∘ mul₁ ← ass) where open Group G

  centralizer-subgroup : ∀ {S} {F : S → S → S} (G : Group F) (A : S → Set)
    → (∃Az : ∃ z , (A z)) → Subgroup G (Centralizer G A ∃Az)
  centralizer-subgroup G A ∃Az = record {
                           nonempty = Re ;
                           closed-· = closed-·-proof ;
                           closed-⁻¹ = closed-⁻¹-proof
                           }
    where
      open Group G
      R = Centralizer G A ∃Az
      Re : R e
      Re = λ Aa → identᵢ₁▶ ∘ identₑ₂▶ ← _==_.reflexive-==
      lemma₁ : ∀ {x} → R x → (∀ {a} → A a → (x · (a · x ⁻¹)) == a)
      lemma₁ Rx = λ Aa → invₑ₁₂▶ ∘ assoc₁◆ ∘ mul₁ ∘ Rx ← Aa
      lemma₂ : ∀ {x a b c} → (x · (a · x ⁻¹)) == c → b == a → (x · (b · x ⁻¹)) == c
      lemma₂ ass eq = euclidean-== (mul₂ ∘ mul₁ ∘ symmetric-== ← eq) ass
      lemma₃ : ∀ {x y} → R x → R y → (∀ {a} → A a → (x · ((y · (a · y ⁻¹)) · x ⁻¹)) == a)
      lemma₃ Rx Ry = λ Aa → (lemma₂ ((lemma₁ Rx) Aa) ((lemma₁ Ry) Aa))
      lemma₄ : ∀ {x y a} → (x · ((y · (a · y ⁻¹)) · x ⁻¹)) == a → ((x · y) · (a · (x · y) ⁻¹)) == a
      lemma₄ ass = euclidean-== (assoc₁▶ (transitive-== ((assoc₂▶ ∘ assoc₂▶ ∘ mul₂) (transitive-== associative (mul₂ associative))) (mul₂ ∘ symmetric-== ← [a·b]⁻¹==b⁻¹·a⁻¹))) ass
      lemma₅ : ∀ {x y a} → (x · ((y · (a · y ⁻¹)) · x ⁻¹)) == a → ((x · y) · a) == (a · (x · y))
      lemma₅ ass = (alternative-centralizer G) (lemma₄ ass)
      closed-·-proof : ∀ {x y} → R x ∧ R y → R (x · y)
      closed-·-proof Rx∧Ry = λ Aa → lemma₅ ((lemma₃ (∧-elim₁ Rx∧Ry) (∧-elim₂ Rx∧Ry)) Aa)
      closed-⁻¹-proof : ∀ {x} → R x → R (x ⁻¹)
      closed-⁻¹-proof Rx = λ Aa → symmetric-== ∘ invₑ₁₂▶ ∘ assoc₁▶ ∘ mul₁ ∘ invₑ₂₁◀ ∘ assoc₂◆ ∘ mul₂ ∘ Rx ← Aa

  Center : ∀ {S} {F : S → S → S} (G : Group F) → S → Set
  Center G g = Centralizer G _∈S (e ∵ all) g where open Group G

  -- Center is a subgroup
  center-subgroup : ∀ {S} {F : S → S → S} (G : Group F) → Subgroup G (Center G)
  center-subgroup G = centralizer-subgroup G _∈S (e ∵ all) where open Group G

  Normalizer : ∀ {S} {F : S → S → S} (G : Group F) (A : S → Set) → ∃ z , (A z) → S → Set
  Normalizer G A ∃Az g = ∀ {a} → A (g · (a · g ⁻¹)) where open Group G

  Stabilizer : ∀ {A S} {F : A → A → A} {φ : A → S → S} (G : Group F) → Action G S φ → (s : S) → (g : A) → Set
  Stabilizer G A s g = φ g s == s where open Action A 
