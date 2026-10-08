/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Projection
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders

/-!
# Distinct challenges in the quadratic near-Johnson construction

The two coefficients immediately below the leading locator term determine a
codimension-two subgroup.  Over a proper field extension, adjoining the fixed
exterior coefficient `θ` makes the resulting challenges injective.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticConstruction

open Polynomial

/-- The coefficient of `X^(2K)` in a size-`4K` binary locator. -/
noncomputable def locatorCoeffA {B : Type*} [Field B]
    (W : AddSubgroup B) [Fintype W] (K : ℕ) : B :=
  (subspacePolynomial W).coeff (2 * K)

/-- The coefficient of `X^K` in a size-`4K` binary locator. -/
noncomputable def locatorCoeffB {B : Type*} [Field B]
    (W : AddSubgroup B) [Fintype W] (K : ℕ) : B :=
  (subspacePolynomial W).coeff K

/-- Equality of the two displayed sparse locator coefficients forces equality
of size-`4K` subgroups inside a size-`16K` binary domain. -/
theorem eq_of_locatorCoeffA_eq_and_locatorCoeffB_eq
    {B : Type*} [Field B] [Fintype B] [CharP B 2]
    (D W₁ W₂ : AddSubgroup B) [Fintype W₁] [Fintype W₂]
    (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K)
    (hW₁ : Nat.card W₁ = 4 * K) (hW₂ : Nat.card W₂ = 4 * K)
    (hle₁ : W₁ ≤ D) (hle₂ : W₂ ≤ D)
    (ha : locatorCoeffA W₁ K = locatorCoeffA W₂ K)
    (hb : locatorCoeffB W₁ K = locatorCoeffB W₂ K) :
    W₁ = W₂ := by
  classical
  let _ : Algebra (ZMod 2) B := ZMod.algebra B 2
  obtain ⟨k, rfl⟩ := hpow
  cases k with
  | zero => simp at hK
  | succ m =>
    have h4 : 4 * 2 ^ (m + 1) = 2 ^ (m + 3) := by
      simp only [pow_succ]
      ring
    have hc₁ : Fintype.card W₁ = 2 ^ (m + 3) := by
      rw [← Nat.card_eq_fintype_card, hW₁, h4]
    have hc₂ : Fintype.card W₂ = 2 ^ (m + 3) := by
      rw [← Nat.card_eq_fintype_card, hW₂, h4]
    obtain ⟨V₁, hd₁, _, hs₁⟩ := subspacePolynomial_three_term_shape W₁ m hc₁
    obtain ⟨V₂, hd₂, _, hs₂⟩ := subspacePolynomial_three_term_shape W₂ m hc₂
    have h2K : 2 * 2 ^ (m + 1) = 2 ^ (m + 2) := by
      simp only [pow_succ]
      ring
    have hdiff : subspacePolynomial W₁ - subspacePolynomial W₂ = V₁ - V₂ := by
      rw [hs₁, hs₂]
      simp only [locatorCoeffA, locatorCoeffB] at ha hb
      rw [h2K] at ha
      rw [ha, hb]
      ring
    by_contra hne
    have hpoly_ne : subspacePolynomial W₁ - subspacePolynomial W₂ ≠ 0 := by
      intro hz
      apply hne
      apply subspacePolynomial_injective W₁ W₂
      exact sub_eq_zero.mp hz
    let S := additiveDomain (W₁ ⊓ W₂)
    have hroot : S.filter (fun x ↦ (subspacePolynomial W₁ -
        subspacePolynomial W₂).eval x = 0) = S := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      have hx' : x ∈ W₁ ⊓ W₂ := by simpa [S, additiveDomain] using hx
      simp only [eval_sub]
      rw [(subspacePolynomial_eval_eq_zero_iff W₁ x).mpr hx'.1,
        (subspacePolynomial_eval_eq_zero_iff W₂ x).mpr hx'.2, sub_self]
    have hdeg : (subspacePolynomial W₁ - subspacePolynomial W₂).natDegree ≤ 2 ^ m := by
      rw [hdiff]
      exact (natDegree_sub_le V₁ V₂).trans (max_le hd₁ hd₂)
    have hupper := card_filter_eval_eq_zero_le S
      (subspacePolynomial W₁ - subspacePolynomial W₂) hpoly_ne
    rw [hroot] at hupper
    have hinter : 2 ^ (m + 1) ≤ Nat.card ↥(W₁ ⊓ W₂) :=
      card_le_inf_of_card_eq_four_mul D W₁ W₂ (2 ^ (m + 1)) (by positivity)
        hD hW₁ hW₂ hle₁ hle₂
    have hScard : S.card = Nat.card ↥(W₁ ⊓ W₂) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    rw [hScard] at hupper
    omega

/-- The challenge attached to a codimension-two locator. -/
noncomputable def locatorLabel
    {B F : Type*} [Field B] [Field F]
    (φ : B →+* F) (θ : F) (W : AddSubgroup B) [Fintype W] (K : ℕ) : F :=
  φ (locatorCoeffA W K ^ 3 + locatorCoeffB W K ^ 2) +
    θ * φ (locatorCoeffA W K)

/-- Over a proper extension, the quadratic construction's challenge is
injective on the size-`4K` subgroups in the prescribed domain. -/
theorem eq_of_locatorLabel_eq
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ ∉ Set.range φ)
    (D W₁ W₂ : AddSubgroup B) [Fintype W₁] [Fintype W₂]
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K)
    (hW₁ : Nat.card W₁ = 4 * K) (hW₂ : Nat.card W₂ = 4 * K)
    (hle₁ : W₁ ≤ D) (hle₂ : W₂ ≤ D)
    (hlabel : locatorLabel φ θ W₁ K = locatorLabel φ θ W₂ K) :
    W₁ = W₂ := by
  let _ : Algebra B F := φ.toAlgebra
  have halg : algebraMap B F = φ := RingHom.algebraMap_toAlgebra φ
  have hθ' : θ ∉ Set.range (algebraMap B F) := by rw [halg]; exact hθ
  obtain ⟨l0, l1, hl01, hl0θ, hl11, hl1θ⟩ := exists_extension_coordinates θ hθ'
  have hmap (l : F →ₗ[B] B) (a : B) (b : F) :
      l (algebraMap B F a * b) = a * l b := by
    simpa [Algebra.smul_def] using l.map_smul a b
  have hmapφ (l : F →ₗ[B] B) (a : B) (b : F) :
      l (φ a * b) = a * l b := by
    rw [← halg]
    exact hmap l a b
  have hl0 (a : B) : l0 (φ a) = a := by
    simpa [hl01] using hmapφ l0 a 1
  have hl1 (a : B) : l1 (φ a) = 0 := by
    simpa [hl11] using hmapφ l1 a 1
  have hl0pow (a : B) (n : ℕ) : l0 (φ a ^ n) = a ^ n := by
    rw [← map_pow, hl0]
  have hl1pow (a : B) (n : ℕ) : l1 (φ a ^ n) = 0 := by
    rw [← map_pow, hl1]
  have ha : locatorCoeffA W₁ K = locatorCoeffA W₂ K := by
    have he := congrArg l1 hlabel
    simp only [locatorLabel, map_add] at he
    simpa [hl1pow, hmapφ, hl1θ, mul_comm θ] using he
  have hab :
      locatorCoeffA W₁ K ^ 3 + locatorCoeffB W₁ K ^ 2 =
        locatorCoeffA W₂ K ^ 3 + locatorCoeffB W₂ K ^ 2 := by
    have he := congrArg l0 hlabel
    simp only [locatorLabel, map_add] at he
    simpa [hl0pow, hmapφ, hl0θ, mul_comm θ] using he
  have hbpow : locatorCoeffB W₁ K ^ 2 = locatorCoeffB W₂ K ^ 2 := by
    simpa [ha] using hab
  have hb : locatorCoeffB W₁ K = locatorCoeffB W₂ K := CharTwo.sq_injective hbpow
  exact eq_of_locatorCoeffA_eq_and_locatorCoeffB_eq D W₁ W₂ K hK hpow
    hD hW₁ hW₂ hle₁ hle₂ ha hb

/-- The locator challenge with the finite structure on the subgroup chosen
canonically from the finite ambient field.  This form is convenient when
mapping a finite family of subgroups. -/
noncomputable def finiteLocatorLabel
    {B F : Type*} [Field B] [Finite B] [Field F]
    (φ : B →+* F) (θ : F) (K : ℕ) (W : AddSubgroup B) : F := by
  letI : Fintype W := Fintype.ofFinite W
  exact locatorLabel φ θ W K

/-- The exterior-coordinate challenges are injective on any finite family of
size-`4K` subgroups contained in the prescribed size-`16K` domain. -/
theorem finiteLocatorLabel_injOn
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2]
    (φ : B →+* F) (θ : F) (hθ : θ ∉ Set.range φ)
    (D : AddSubgroup B) (S : Finset (AddSubgroup B))
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K)
    (hcard : ∀ W ∈ S, Nat.card W = 4 * K)
    (hle : ∀ W ∈ S, W ≤ D) :
    Set.InjOn (finiteLocatorLabel φ θ K) S := by
  intro W₁ hW₁ W₂ hW₂ he
  let _ : Fintype W₁ := Fintype.ofFinite W₁
  let _ : Fintype W₂ := Fintype.ofFinite W₂
  apply eq_of_locatorLabel_eq φ θ hθ D W₁ W₂ K hK hpow hD
    (hcard W₁ hW₁) (hcard W₂ hW₂) (hle W₁ hW₁) (hle W₂ hW₂)
  simpa only [finiteLocatorLabel] using he

/-- Mapping a suitable finite subgroup family to exterior-coordinate challenges
does not decrease its cardinality. -/
theorem card_image_finiteLocatorLabel
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2] [DecidableEq F]
    (φ : B →+* F) (θ : F) (hθ : θ ∉ Set.range φ)
    (D : AddSubgroup B) (S : Finset (AddSubgroup B))
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K)
    (hcard : ∀ W ∈ S, Nat.card W = 4 * K)
    (hle : ∀ W ∈ S, W ≤ D) :
    (S.image (finiteLocatorLabel φ θ K)).card = S.card := by
  classical
  rw [Finset.card_image_iff]
  exact finiteLocatorLabel_injOn φ θ hθ D S K hK hpow hD hcard hle

/-- The codimension-two binary family supplies the paper's explicit number
of distinct exterior-coordinate challenges. -/
theorem codimTwo_label_count_lower_bound
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [CharP F 2] [DecidableEq F] [Module (ZMod 2) B]
    (φ : B →+* F) (θ : F) (hθ : θ ∉ Set.range φ)
    (D : AddSubgroup B)
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hD : Nat.card D = 16 * K) :
    (Nat.card D - 1) * (Nat.card D - 2) / 6 ≤
      ((codimTwoBinarySubspaces D).image (finiteLocatorLabel φ θ K)).card := by
  classical
  rw [card_image_finiteLocatorLabel φ θ hθ D (codimTwoBinarySubspaces D) K hK hpow hD
    (fun W hW ↦ by rw [natCard_codimTwoBinarySubspace D W hW, hD]; omega)
    (fun W hW ↦ codimTwoBinarySubspaces_le D W hW)]
  apply codimTwoBinarySubspaces_count_lower_bound D
  by_contra hdim
  have hdim' : Module.finrank (ZMod 2) D ≤ 1 := by omega
  have hcardpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
  have htwo : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [htwo, hD] at hcardpow
  interval_cases Module.finrank (ZMod 2) D
  all_goals norm_num at hcardpow
  all_goals omega

end BinaryFieldCounterexamples.QuadraticConstruction
