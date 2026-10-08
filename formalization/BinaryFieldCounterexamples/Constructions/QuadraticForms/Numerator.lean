/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Canonical prime-power numerators for the first input

Remove the linear term of a polynomial supported in powers of `p^r`, then
extract its canonical `p^r`th root using inverse Frobenius on coefficients.
The resulting numerator has constant derivative and the degree bound needed
by the Wronskian argument for the first input of Lemma 3.13. Support of the actual
domain locator is a separate hypothesis, not inferred from a desired root count.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial

/-- Coefficientwise inverse Frobenius, with exponents divided by the prime power. -/
noncomputable def primePowerPolynomialRoot
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (P : F[X]) : F[X] :=
  P.sum fun n a => monomial (n / p^r) ((iterateFrobeniusEquiv F p r).symm a)

/-- The canonical root recovers a polynomial whose support exponents are divisible by the prime power. -/
theorem primePowerPolynomialRoot_pow
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (P : F[X]) (hs : ∀ n ∈ P.support, p^r ∣ n) :
    primePowerPolynomialRoot p r P ^ (p^r) = P := by
  classical
  rw [primePowerPolynomialRoot, Polynomial.sum_def, sum_pow_char_pow]
  conv_rhs => rw [P.as_sum_support]
  apply Finset.sum_congr rfl
  intro n hn
  rw [monomial_pow, Nat.div_mul_cancel (hs n hn)]
  congr 1
  rw [← iterateFrobeniusEquiv_def]
  exact (iterateFrobeniusEquiv F p r).apply_symm_apply (P.coeff n)

/-- Every root-support exponent arises by dividing an original support exponent. -/
theorem primePowerPolynomialRoot_support
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (P : F[X]) (n : ℕ) (hn : n ∈ (primePowerPolynomialRoot p r P).support) :
    ∃ m ∈ P.support, n = m / p^r := by
  classical
  rw [mem_support_iff] at hn
  simp only [primePowerPolynomialRoot, coeff_sum, coeff_monomial] at hn
  by_contra h
  simp only [not_exists, not_and] at h
  apply hn
  apply Finset.sum_eq_zero
  intro m hm
  simp only [ite_eq_right (Ne.symm (h m hm))]

/-- The domain polynomial with its linear term removed and the pole constant inserted. -/
noncomputable def primePowerQuarterRadicand
    {F : Type*} [Field F] (L : F[X]) (β : F) : F[X] :=
  L - C (L.coeff 1) * (X - C β)

/-- Removing the linear term leaves a constant and positive prime-power exponents. -/
theorem primePowerQuarterRadicand_support
    {F : Type*} [Field F] (b : ℕ) (_hb : 2 ≤ b) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, ∃ i : ℕ, n = b^i)
    (n : ℕ) (hn : n ∈ (primePowerQuarterRadicand L β).support) :
    n = 0 ∨ ∃ i : ℕ, n = b^(i+1) := by
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  have hncoeff := mem_support_iff.mp hn
  by_cases hn1 : n = 1
  · subst n
    simp [primePowerQuarterRadicand] at hncoeff
  have hshape : primePowerQuarterRadicand L β = L - C (L.coeff 1) * X +
      C (L.coeff 1 * β) := by
    simp only [primePowerQuarterRadicand]
    rw [mul_sub, ← C_mul]
    ring
  rw [hshape] at hncoeff
  have hLn : L.coeff n ≠ 0 := by
    simpa [coeff_sub, coeff_add, coeff_C_mul, coeff_X, hn1, Ne.symm hn1,
      coeff_C, hn0] using hncoeff
  obtain ⟨i, hi⟩ := hs n (mem_support_iff.mpr hLn)
  cases i with
  | zero => simp at hi; exact (hn1 hi).elim
  | succ i => exact Or.inr ⟨i, hi⟩

/-- The canonical prime-power numerator for the first input of Lemma 3.13. -/
noncomputable def primePowerQuarterNumerator
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (L : F[X]) (β : F) : F[X] :=
  primePowerPolynomialRoot p r (primePowerQuarterRadicand L β)

/-- The canonical numerator satisfies the required Frobenius identity. -/
theorem primePowerQuarterNumerator_pow
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, ∃ i : ℕ, n = (p^r)^i) :
    primePowerQuarterNumerator p r L β ^ (p^r) = primePowerQuarterRadicand L β := by
  apply primePowerPolynomialRoot_pow
  intro n hn
  have hb : 2 ≤ p^r := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  rcases primePowerQuarterRadicand_support (p^r) hb L β hs n hn with hz | ⟨i, hi⟩
  · simp [hz]
  · rw [hi, pow_succ]
    exact dvd_mul_left _ _

/-- Taking the Frobenius root preserves affine prime-power support. -/
theorem primePowerQuarterNumerator_support
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, ∃ i : ℕ, n = (p^r)^i)
    (n : ℕ) (hn : n ∈ (primePowerQuarterNumerator p r L β).support) :
    n = 0 ∨ ∃ i : ℕ, n = (p^r)^i := by
  obtain ⟨m, hm, rfl⟩ := primePowerPolynomialRoot_support p r _ n hn
  have hb : 2 ≤ p^r := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  rcases primePowerQuarterRadicand_support (p^r) hb L β hs m hm with hz | ⟨i, hi⟩
  · simp [hz]
  · right
    refine ⟨i, ?_⟩
    rw [hi, pow_succ, Nat.mul_div_cancel]
    omega

/-- Affine prime-power support forces the formal derivative to be constant. -/
theorem derivative_eq_C_of_primePowerAffineSupport
    {F : Type*} [Field F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (P : F[X])
    (hs : ∀ n ∈ P.support, n = 0 ∨ ∃ i : ℕ, n = (p^r)^i) :
    P.derivative = C (P.coeff 1) := by
  ext n
  cases n with
  | zero => simp [coeff_derivative]
  | succ n =>
      rw [coeff_derivative, coeff_C]
      simp only [Nat.succ_ne_zero, ite_false]
      by_cases hc : P.coeff (n + 1 + 1) = 0
      · simp [hc]
      rcases hs (n+1+1) (mem_support_iff.mpr hc) with hz | ⟨i, hi⟩
      · omega
      have hi0 : i ≠ 0 := by intro h; simp [h] at hi
      have hcast : ((n+1+1 : ℕ) : F) = 0 := by
        rw [hi, Nat.cast_pow, Nat.cast_pow]
        simp [show r ≠ 0 by omega, hi0]
      simpa only [Nat.cast_add, Nat.cast_one, mul_zero] using
        congrArg (P.coeff (n+1+1) * ·) hcast

/-- The canonical first-input numerator has constant formal derivative. -/
theorem primePowerQuarterNumerator_derivative
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, ∃ i : ℕ, n = (p^r)^i) :
    (primePowerQuarterNumerator p r L β).derivative =
      C ((primePowerQuarterNumerator p r L β).coeff 1) := by
  exact derivative_eq_C_of_primePowerAffineSupport p r hr _
    (primePowerQuarterNumerator_support p r hr L β hs)

/-- A domain-degree bound descends through the Frobenius root. -/
theorem primePowerQuarterNumerator_natDegree_le
    {F : Type*} [Field F] [Fintype F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L : F[X]) (β : F)
    (hs : ∀ n ∈ L.support, ∃ i : ℕ, n = (p^r)^i)
    (K : ℕ) (hK : 1 ≤ K) (hL : L.natDegree ≤ (p^r)^2*K) :
    (primePowerQuarterNumerator p r L β).natDegree ≤ p^r*K := by
  have hb : 2 ≤ p^r := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hrad : (primePowerQuarterRadicand L β).natDegree ≤ (p^r)^2*K := by
    apply (natDegree_sub_le _ _).trans
    refine max_le hL ?_
    exact natDegree_mul_le.trans (by simp; nlinarith)
  rw [← primePowerQuarterNumerator_pow p r hr L β hs, natDegree_pow] at hrad
  nlinarith

end BinaryFieldCounterexamples
