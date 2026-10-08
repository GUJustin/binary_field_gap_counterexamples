/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Compression

/-!
# Moment equations and the coefficients of the Gold derivative

This module completes the converses in Lemma 5.8, p. 41 of the
[paper](../../../../binary-field-counterexamples.pdf#page=41)
(`lem:gold-window`, “Moment equations and the coefficients of J”).
The low coefficients recover the moments by the unit-diagonal expansion.
At the high end, the weighted recurrence propagates coefficient vanishing
upward, and the nonzero top scaling factor recovers the next moment.

The final theorem packages all three conditions, the equivalent degree bound,
and the displayed window and inverse-Frobenius formula. No rank assumption or
choice of a basis is needed: the identities hold for arbitrary tensor coordinates
and arbitrary labels in the parameter domain, hence in particular for the
paper's basis of the label space.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- The unit-diagonal low-coefficient expansion recovers every initial Gold moment. -/
theorem goldMoment_eq_zero_of_low_coefficients (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (t : ℕ)
    (hJ : ∀ i, 1 ≤ i → i < t → (tensorLinearPart D v A).coeff (2^i) = 0) :
    ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr hrt
    have he := tensorLinearPart_coeff_expansion D v A r
    rw [hJ r hr hrt, Finset.sum_range_succ] at he
    have hsum : ∑ s ∈ Finset.range r,
        (normalizedLocator D).coeff (2^(r-s)) ^ (2^s) * goldMoment D v A s ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hsr := Finset.mem_range.mp hs
      have hM : goldMoment D v A s = 0 := by
        by_cases hs0 : s = 0
        · subst s; exact goldMoment_zero D v A
        · exact ih s hsr (by omega) (by omega)
      rw [hM, zero_pow (by decide), mul_zero]
    simp only [hsum, Nat.sub_self, pow_zero, normalizedLocator_coeff_one, one_pow,
      zero_add, one_mul] at he
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp he.symm

/-- If the intervening moments vanish, a zero weighted coefficient propagates upward. -/
theorem weightedCoefficient_eq_zero_upward (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (i r s : ℕ) (hW : weightedCoefficient D v A i r = 0)
    (hM : ∀ j, r ≤ j → j < r+s → goldMoment D v A j = 0) :
    weightedCoefficient D v A (i+s) (r+s) = 0 := by
  induction s with
  | zero => simpa using hW
  | succ s ih =>
    have hprev := ih (fun j hj hj' ↦ hM j hj (by omega))
    rw [show i+(s+1) = (i+s)+1 by omega, show r+(s+1) = (r+s)+1 by omega,
      weightedCoefficient_recurrence, hprev, hM (r+s) (by omega) (by omega)]
    simp

/-- The nonzero top scaling factor and weighted recurrence recover moments from
vanishing high coefficients. The domain has dimension `k+1`. -/
theorem goldMoment_eq_zero_of_high_coefficients (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (t : ℕ) (ht : t ≤ k+1)
    (hJ : ∀ i, k+2-t ≤ i → i ≤ k → (tensorLinearPart D v A).coeff (2^i) = 0) :
    ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr hrt
    have hW : weightedCoefficient D v A (k-(r-1)) 1 = 0 := by
      rw [weightedCoefficient_one]
      exact hJ _ (by omega) (by omega)
    have htop := weightedCoefficient_eq_zero_upward D v A (k-(r-1)) 1 (r-1) hW
      (fun j hj hj' ↦ ih j (by omega) hj (by omega))
    rw [show k-(r-1)+(r-1) = k by omega, show 1+(r-1) = r by omega,
      weightedCoefficient_top D k hD] at htop
    exact (mul_eq_zero.mp htop).resolve_left (normalizingRoot_ne_zero D)

/-- Initial moment equations are equivalent to vanishing initial nontrivial
binary coefficients, without any dimension or rank restriction. -/
theorem goldMoment_iff_low_coefficients (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (t : ℕ) :
    (∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) ↔
      (∀ i, 1 ≤ i → i < t → (tensorLinearPart D v A).coeff (2^i) = 0) := by
  constructor
  · intro hM i _ hi; exact tensorLinearPart_coeff_eq_zero D v A t hM i hi
  · exact goldMoment_eq_zero_of_low_coefficients D v A t

/-- Initial moment equations are equivalent to vanishing final binary
coefficients, for a domain of dimension `d` and `t ≤ d`. -/
theorem goldMoment_iff_high_coefficients (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hd : 1 ≤ d) (hD : Nat.card D = 2^d) {n : ℕ}
    (v : Fin n → parameterDomain D) (A : TensorCoordinates n) (t : ℕ) (ht : t ≤ d) :
    (∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) ↔
      (∀ i, d-t+1 ≤ i → i < d → (tensorLinearPart D v A).coeff (2^i) = 0) := by
  have hD' : Nat.card D = 2^((d-1)+1) := by simpa [Nat.sub_add_cancel hd] using hD
  constructor
  · intro hM i hlo hhi
    exact tensorLinearPart_high_coeff_eq_zero D (d-1) hD' v A t hM i (d-1-i)
      (by omega) (by omega)
  · intro hJ
    apply goldMoment_eq_zero_of_high_coefficients D (d-1) hD' v A t (by omega)
    intro i hlo hhi
    exact hJ i (by omega) (by omega)

/-- The paper's high-coefficient condition is exactly its polynomial degree bound.
The use of `degree` includes the zero polynomial. -/
theorem high_coefficients_iff_degree_le (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hd : 1 ≤ d) (hD : Nat.card D = 2^d) {n : ℕ}
    (v : Fin n → parameterDomain D) (A : TensorCoordinates n) (t : ℕ) (ht : t ≤ d) :
    (∀ i, d-t+1 ≤ i → i < d → (tensorLinearPart D v A).coeff (2^i) = 0) ↔
      (tensorLinearPart D v A).degree ≤ (2^(d-t) : ℕ) := by
  rw [← natDegree_le_iff_degree_le]
  constructor
  · intro hJ
    have hM := (goldMoment_iff_high_coefficients D d hd hD v A t ht).mpr hJ
    simpa [Nat.sub_add_cancel hd] using tensorLinearPart_natDegree_le D (d-1)
      (by simpa [Nat.sub_add_cancel hd] using hD) v A t hM
  · intro hdeg i hlo _
    apply coeff_eq_zero_of_natDegree_lt
    exact hdeg.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- Under the moment equations, `J` is literally the sum of its binary monomials
in the closed interval `[t, d-t]`, as in equation `eq:gold-J-window`. -/
theorem tensorLinearPart_eq_window (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hd : 1 ≤ d) (hD : Nat.card D = 2^d) {n : ℕ}
    (v : Fin n → parameterDomain D) (A : TensorCoordinates n) (t : ℕ)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) :
    tensorLinearPart D v A = ∑ i ∈ Finset.Icc t (d-t),
      monomial (2^i) ((tensorLinearPart D v A).coeff (2^i)) := by
  classical
  have hsupport : ∀ m ∈ (tensorLinearPart D v A).support,
      ∃ i ∈ Finset.Icc t (d-t), m = 2^i := by
    intro m hm
    obtain ⟨i, hi, hlo, hhi⟩ := tensorLinearPart_support_interval D (d-1)
      (by simpa [Nat.sub_add_cancel hd] using hD) v A t hM m hm
    exact ⟨i, Finset.mem_Icc.mpr ⟨hlo, by simpa [Nat.sub_add_cancel hd] using hhi⟩, hi⟩
  ext m
  rw [finsetSum_coeff]
  by_cases hm : ∃ i ∈ Finset.Icc t (d-t), m = 2^i
  · obtain ⟨i, hi, rfl⟩ := hm
    rw [Finset.sum_eq_single i, coeff_monomial_same]
    · intro j _ hji
      rw [coeff_monomial, ite_eq_right]
      exact fun h ↦ hji (Nat.pow_right_injective (by decide : 2 ≤ 2) h)
    · exact fun h ↦ (h hi).elim
  · have hz : (tensorLinearPart D v A).coeff m = 0 := by
      by_contra hne
      exact hm (hsupport m (mem_support_iff.mpr hne))
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_monomial, ite_eq_right]
    exact fun h ↦ hm ⟨i, hi, h.symm⟩

/-- The Frobenius root has exactly the paper's inverse-Frobenius coefficients
and contracted binary exponents. -/
theorem tensorLinearPart_frobeniusRoot_eq_window (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hd : 1 ≤ d) (hD : Nat.card D = 2^d) {n : ℕ}
    (v : Fin n → parameterDomain D) (A : TensorCoordinates n) (t : ℕ)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) :
    frobeniusRoot t (tensorLinearPart D v A) = ∑ i ∈ Finset.Icc t (d-t),
      monomial (2^(i-t))
        ((iterateFrobeniusEquiv B 2 t).symm ((tensorLinearPart D v A).coeff (2^i))) := by
  classical
  ext m
  rw [frobeniusRoot, coeff_map, coeff_contract (by positivity)]
  conv_lhs => rw [tensorLinearPart_eq_window D d hd hD v A t hM, finsetSum_coeff]
  rw [map_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hti := (Finset.mem_Icc.mp hi).1
  have hexp : 2^i = 2^(i-t)*2^t := by rw [← pow_add, Nat.sub_add_cancel hti]
  have he : 2^i = m*2^t ↔ 2^(i-t) = m := by
    rw [hexp]
    exact Nat.mul_right_cancel_iff (by positivity)
  simp only [coeff_monomial, he]
  split_ifs <;> simp

/-- **Lemma 5.8 (Moment equations and the coefficients of `J`), p. 41.**
For a binary additive domain of size `N = 2^d` and `2 ≤ t ≤ d/2`, the
initial moments vanish iff the low coefficients vanish iff the high coefficients
vanish; the latter is exactly `deg J ≤ N/2^t`. Also `J₀ = 0`.

Whenever these conditions hold, the theorem gives the two explicit sums in
equation `eq:gold-J-window`, `J = Ĵ^(2^t)`, and `deg Ĵ ≤ N/2^(2*t)`.
Here `J` is `tensorLinearPart`, `Ĵ` is `frobeniusRoot t J`, and the inverse
Frobenius equivalence is the unique `2^t`-th root operation in the finite field.
The tensor stores the upper-triangular entries of the alternating binary matrix;
the result holds for all parameter labels, including every basis in the paper. -/
theorem gold_moment_window_iff (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hD : Nat.card D = 2^d)
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht2 : 2 ≤ t) (htd : t ≤ d/2) :
    let J := tensorLinearPart D v A
    let Jhat := frobeniusRoot t J
    let moments := ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0
    let low := ∀ i, 1 ≤ i → i < t → J.coeff (2^i) = 0
    let high := ∀ i, d-t+1 ≤ i → i < d → J.coeff (2^i) = 0
    J.coeff 1 = 0 ∧ (moments ↔ low) ∧ (moments ↔ high) ∧
      (high ↔ J.degree ≤ (Nat.card D / 2^t : ℕ)) ∧
      (moments →
        J = (∑ i ∈ Finset.Icc t (d-t), monomial (2^i) (J.coeff (2^i))) ∧
        J = Jhat ^ (2^t) ∧
        Jhat = (∑ i ∈ Finset.Icc t (d-t),
          monomial (2^(i-t)) ((iterateFrobeniusEquiv B 2 t).symm (J.coeff (2^i)))) ∧
        Jhat.degree ≤ (Nat.card D / 2^(2*t) : ℕ)) := by
  dsimp only
  have hd : 1 ≤ d := by omega
  have ht : t ≤ d := by omega
  have hdt : 2*t ≤ d := by omega
  have hD' : Nat.card D = 2^((d-1)+1) := by simpa [Nat.sub_add_cancel hd] using hD

  -- Recover the moments from either end, and identify the high end with the degree bound.
  refine ⟨?_, goldMoment_iff_low_coefficients D v A t,
    goldMoment_iff_high_coefficients D d hd hD v A t ht, ?_, ?_⟩
  · simpa using tensorLinearPart_coeff_eq_zero D v A 1 (by intro r hr hrt; omega) 0
      (by decide)
  · rw [hD, Nat.pow_div ht (by decide)]
    exact high_coefficients_iff_degree_le D d hd hD v A t ht

  -- The two-sided support interval gives the displayed polynomial and its power root.
  · intro hM
    have hsupport : ∀ m ∈ (tensorLinearPart D v A).support, 2^t ∣ m := by
      intro m hm
      obtain ⟨i, rfl, hi, _⟩ := tensorLinearPart_support_interval D (d-1) hD' v A t hM m hm
      exact pow_dvd_pow 2 hi
    refine ⟨tensorLinearPart_eq_window D d hd hD v A t hM,
      (frobeniusRoot_pow t _ hsupport).symm,
      tensorLinearPart_frobeniusRoot_eq_window D d hd hD v A t hM, ?_⟩
    rw [hD, Nat.pow_div hdt (by decide)]
    apply degree_le_of_natDegree_le
    apply frobeniusRoot_natDegree_le
    have he : (d-1)+1-t = (d-2*t)+t := by omega
    simpa only [he, pow_add] using tensorLinearPart_natDegree_le D (d-1) hD' v A t hM

end BinaryFieldCounterexamples.Gold
