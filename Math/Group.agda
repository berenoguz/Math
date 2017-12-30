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
  open import Math.Function hiding (_^_)
  open import Math.Logic
  open _∧_
  open import Math.NaturalNumbers using (ℕ ; _<_ ; _′ ; ℕ⁺)
  open import Agda.Primitive using (_⊔_) 
  import Math.Reasoning

  -- Definition of group
  -- Associative binary operation with an identity element and inverses.
  record Group {ℓ} (A : Set ℓ) : Set ℓ where
    constructor Group_∵_∵_
    S = A
    field
      _·_ : S → S → S
      associative : Associative _·_
      identity : Identity _·_
      inverse : Inverse _·_ identity

    -- A relation relating to all members of S
    data _∈S (x : S) : Set ℓ where
      all : x ∈S

    -- Reasoning Helpers
    open Math.Reasoning.Associative _·_ associative public
    open Math.Reasoning.Identity _·_ identity public
    open Math.Reasoning.Binary-Operation _·_ public
    open Math.Reasoning.Inverse _·_ identity inverse public

    -- Identity Theorems
    unique-identity : Unique-Identity _·_ -- Group identity is unique
    unique-identity = e ∵ identity-e ∵ unique-e
      where
        unique-e : ∀ {e′} → (∀ {x : S} → ((x · e′) ≡ x) ∧ ((e′ · x) ≡ x)) → e′ ≡ e
        unique-e identity-e′ = identₑ₂◀ (∧ₑᵣ identity-e′)
    unique-e = ∃!.uniqueness unique-identity -- Proof that e is unique

    -- Inverse Theorems
    a⁻¹·a⁻¹⁻¹≡a·a⁻¹ : ∀ {a} → (a ⁻¹ · a ⁻¹ ⁻¹) ≡ (a ⁻¹ · a)
    a⁻¹·a⁻¹⁻¹≡a·a⁻¹ = left-euclidean-≡ (∧ₑᵣ (∃.proof inverse)) (∧ₑₗ (∃.proof inverse))

    a·a⁻¹≡a⁻¹·a⁻¹⁻¹ : ∀ {a} → (a ⁻¹ · a) ≡ (a ⁻¹ · a ⁻¹ ⁻¹)
    a·a⁻¹≡a⁻¹·a⁻¹⁻¹ = symmetric-≡ a⁻¹·a⁻¹⁻¹≡a·a⁻¹

    -- For each group element, its inverse is unique
    unique-inverse : Unique-Inverse _·_ identity
    unique-inverse = ∃.witness inverse ∵ ∃.proof inverse ∵ uniqueness
      where
        lemma : ∀ {x inv} → (x ⁻¹ · (x · inv)) ≡ inv
        lemma = assoc₁◀ (identₑ₂▶ (mul₁ (∧ₑₗ (∃.proof inverse))))
        uniqueness : ∀ {x inv} → ((x · inv) ≡ e) ∧ ((inv · x) ≡ e) → inv ≡ x ⁻¹
        uniqueness ass = symmetric-≡ (identₑ₁◀ (euclidean-≡ (mul₂ (∧ₑᵣ ass)) lemma))
  
    -- Inverse of inverse of a is a
    a⁻¹⁻¹≡a : ∀ {a} → a ⁻¹ ⁻¹ ≡ a
    a⁻¹⁻¹≡a = left-euclidean-≡ (euclidean-≡ lemma (mul₂ a⁻¹·a⁻¹⁻¹≡a·a⁻¹)) (symmetric-≡ lemma)
      where
        lemma : ∀ {a t} → (a · (a ⁻¹ · t)) ≡ t
        lemma = assoc₁◀ (left-euclidean-≡ (mul₁ (∧ₑᵣ (∃.proof inverse))) (symmetric-≡ (∧ₑₗ (∃.proof identity))))

    [a·b]⁻¹≡b⁻¹·a⁻¹ : ∀ {a b} → (a · b) ⁻¹ ≡ (b ⁻¹ · a ⁻¹)
    [a·b]⁻¹≡b⁻¹·a⁻¹ = symmetric-≡ (left-euclidean-≡ (left-euclidean-≡ (mul₂ lemma₂) associative) (euclidean-≡ (∧ₑₗ (∃.proof identity)) (mul₁ (symmetric-≡ (∧ₑₗ (∃.proof inverse))))))
      where
        lemma₁ : ∀ {a b} → a ⁻¹ ≡ (a ⁻¹ · (a · (b · ((a · b) ⁻¹))))
        lemma₁ = symmetric-≡ (left-euclidean-≡ (mul₂ (euclidean-≡ associative (∧ₑᵣ (∃.proof inverse)))) (symmetric-≡ (∧ₑᵣ (∃.proof identity))))
        lemma₂ : ∀ {a b} → a ⁻¹ ≡ (b · ((a · b) ⁻¹))
        lemma₂ = left-euclidean-≡ lemma₁ (euclidean-≡ (∧ₑₗ (∃.proof identity)) (left-euclidean-≡ (mul₁ (symmetric-≡ (∧ₑₗ (∃.proof inverse)))) (symmetric-≡ associative)))
    b⁻¹·a⁻¹≡[a·b]⁻¹ : ∀ {a b} → (b ⁻¹ · a ⁻¹) ≡ (a · b) ⁻¹
    b⁻¹·a⁻¹≡[a·b]⁻¹ = symmetric-≡ [a·b]⁻¹≡b⁻¹·a⁻¹

    -- Cancellation Laws
    cancel₁ : ∀ {a b c} → (a · b) ≡ (a · c) → b ≡ c
    cancel₁ eq = invₑ₂₁◆ (assoc₂◆ (mul₂ eq))
    cancel₂ : ∀ {a b c} → (b · a) ≡ (c · a) → b ≡ c
    cancel₂ eq = invₑ₁₂◆ (assoc₁◆ (mul₁ eq))

    -- Exponentive Notation

    _^_ : S → ℕ → S
    a ^ 0 = e
    a ^ (n ′) = a · (a ^ n)

    -- Order
    record Order (x : S) (n-proof : ℕ⁺) : Set ℓ where
      n = ℕ⁺.value n-proof
      field
        prop₁ : (x ^ n) ≡ e
        minimum : ∀ {m} → (ℕ⁺.value m) < n → (x ^ n) ≠ e
  
  -- Group Homomorphism
  record Homomorphism {ℓ₁ ℓ₂} {S : Set ℓ₁} {T : Set ℓ₂} (G : Group S) (H : Group T) (f : S → T) : Set (ℓ₁ ⊔ ℓ₂) where
      φ = f
      private _★_ = (Group._·_ G)
      private _◇_ = (Group._·_ H)
      field
        homomorphism : ∀ {x y} → φ (x ★ y) ≡ (φ x ◇ φ y)
      kernel = λ g → φ g ≡ (Group.e H)

  -- Group Isomorphism
  record Isomorphism {ℓ} {S T : Set ℓ} (G : Group S) (H : Group T) (f : S → T) : Set ℓ where
      φ = f    
      field
        homomorphism-proof : Homomorphism G H φ
        bijection : Bijection φ
      homomorphism = Homomorphism.homomorphism homomorphism-proof

  record Action {ℓ₁ ℓ₂} {T : Set ℓ₁} (G : Group T) (A : Set ℓ₂) (f : T → A → A) : Set (ℓ₁ ⊔ ℓ₂) where
    open Group G
    φ = f
    field
      prop₁ : ∀ {x y a} → φ x (φ y a) ≡ φ (x · y) a
      prop₂ : ∀ {a} → φ e a ≡ a
    kernel : S → Set ℓ₂
    kernel g = ∀ {s} → φ g s ≡ s

  record Subgroup {ℓ} {T : Set ℓ} (G : Group T) (P : T → Set ℓ) : Set ℓ where
    open Group G
    R = P
    field
      nonempty : R e
      closed-· : ∀ {x y} → R x ∧ R y → R (x · y)
      closed-⁻¹ : ∀ {x} → R x → R (x ⁻¹)

  -- Subgroup Criterion
  subgroup-criterion : ∀ {ℓ} {S : Set ℓ} → (G : Group S) → (R : S → Set ℓ)
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
    Re = subst R (ass (∧ᵢ Rz Rz)) (∧ₑᵣ (∃.proof inverse))
    closed-⁻¹-proof : ∀ {x} → R x →  R (x ⁻¹)
    closed-⁻¹-proof Rx = subst R (ass (∧ᵢ Re Rx)) (identₑ₂▶ _≡_.reflexive-≡)
    lemma : ∀ {x y} → R (y ⁻¹ · x ⁻¹) → R (x · y)
    lemma Ry⁻¹·x⁻¹ = subst R (closed-⁻¹-proof (subst R Ry⁻¹·x⁻¹ b⁻¹·a⁻¹≡[a·b]⁻¹)) a⁻¹⁻¹≡a
    closed-·-proof : ∀ {x y} → R x ∧ R y → R (x · y)
    closed-·-proof (∧ᵢ Rx Ry) = lemma (ass (∧ᵢ (closed-⁻¹-proof Ry) Rx))

  Centralizer : ∀ {ℓ} {S : Set ℓ} (G : Group S) (A : S → Set ℓ) → ∃ z , (A z) → S → Set ℓ
  Centralizer G A ∃Az g = ∀ {a} → A a → (g · a) ≡ (a · g) where open Group G

  -- Alternative definition of centralizer
  alternative-centralizer : ∀ {ℓ} {S : Set ℓ} {g a} → (G : Group S) → ((Group._·_ G) g ((Group._·_ G) a ((Group._⁻¹ G) g))) ≡ a → ((Group._·_ G) g a) ≡ ((Group._·_ G) a g)
  alternative-centralizer G ass = euclidean-≡ (mul₂ ∘ invₑ₂₂▶ ← associative) (assoc₁◀ ∘ mul₁ ← ass) where open Group G

  centralizer-subgroup : ∀ {ℓ} {S : Set ℓ} (G : Group S) (A : S → Set ℓ)
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
      Re = λ Aa → identᵢ₁▶ ∘ identₑ₂▶ ← _≡_.reflexive-≡
      lemma₁ : ∀ {x} → R x → (∀ {a} → A a → (x · (a · x ⁻¹)) ≡ a)
      lemma₁ Rx = λ Aa → invₑ₁₂▶ ∘ assoc₁◆ ∘ mul₁ ∘ Rx ← Aa
      lemma₂ : ∀ {x a b c} → (x · (a · x ⁻¹)) ≡ c → b ≡ a → (x · (b · x ⁻¹)) ≡ c
      lemma₂ ass eq = euclidean-≡ (mul₂ ∘ mul₁ ∘ symmetric-≡ ← eq) ass
      lemma₃ : ∀ {x y} → R x → R y → (∀ {a} → A a → (x · ((y · (a · y ⁻¹)) · x ⁻¹)) ≡ a)
      lemma₃ Rx Ry = λ Aa → (lemma₂ ((lemma₁ Rx) Aa) ((lemma₁ Ry) Aa))
      lemma₄ : ∀ {x y a} → (x · ((y · (a · y ⁻¹)) · x ⁻¹)) ≡ a → ((x · y) · (a · (x · y) ⁻¹)) ≡ a
      lemma₄ ass = euclidean-≡ (assoc₁▶ (transitive-≡ ((assoc₂▶ ∘ assoc₂▶ ∘ mul₂) (transitive-≡ associative (mul₂ associative))) (mul₂ ∘ symmetric-≡ ← [a·b]⁻¹≡b⁻¹·a⁻¹))) ass
      lemma₅ : ∀ {x y a} → (x · ((y · (a · y ⁻¹)) · x ⁻¹)) ≡ a → ((x · y) · a) ≡ (a · (x · y))
      lemma₅ ass = (alternative-centralizer G) (lemma₄ ass)
      closed-·-proof : ∀ {x y} → R x ∧ R y → R (x · y)
      closed-·-proof Rx∧Ry = λ Aa → lemma₅ ((lemma₃ (∧ₑᵣ Rx∧Ry) (∧ₑₗ Rx∧Ry)) Aa)
      closed-⁻¹-proof : ∀ {x} → R x → R (x ⁻¹)
      closed-⁻¹-proof Rx = λ Aa → symmetric-≡ ∘ invₑ₁₂▶ ∘ assoc₁▶ ∘ mul₁ ∘ invₑ₂₁◀ ∘ assoc₂◆ ∘ mul₂ ∘ Rx ← Aa

  Center : ∀ {ℓ} {S : Set ℓ} (G : Group S) → S → Set ℓ
  Center G g = Centralizer G _∈S (e ∵ all) g where open Group G

  -- Center is a subgroup
  center-subgroup : ∀ {ℓ} {S : Set ℓ} (G : Group S) → Subgroup G (Center G)
  center-subgroup G = centralizer-subgroup G _∈S (e ∵ all) where open Group G

  Normalizer : ∀ {ℓ} {S : Set ℓ} (G : Group S) (A : S → Set ℓ) → ∃ z , (A z) → S → Set ℓ
  Normalizer G A ∃Az g = ∀ {a} → A (g · (a · g ⁻¹)) where open Group G

  Stabilizer : ∀ {ℓ₁ ℓ₂} {S : Set ℓ₁} {A : Set ℓ₂} {φ : S → A → A} (G : Group S) → Action G A φ → (s : A) → (g : S) → Set ℓ₂
  Stabilizer G A s g = φ g s ≡ s where open Action A 

  -- Cosets

  Left-Coset : ∀ {S H} (G : Group S) → Subgroup G H → S → S → Set
  Left-Coset G H g h = R (g ⁻¹ · h)
    where
      open Group G
      open Subgroup H

  Normal : ∀ {S H} → (G : Group S) → Subgroup G H → Set
  Normal G H = ∀ {g n} → R n → R (g · (n · g ⁻¹))
    where
      open Group G
      open Subgroup H

  record Quotient-Group {S A} (G : Group S) (H : Subgroup G A) (g : S) : Set where
    N = Subgroup.R H -- Predicate : in subgroup H
    R = λ h → Left-Coset G H g h -- Predicate : in left-coset
    open Group G
    field
      normal : Normal G H
    
