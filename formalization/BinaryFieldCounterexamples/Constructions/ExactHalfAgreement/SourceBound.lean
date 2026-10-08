/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Basic
public import BinaryFieldCounterexamples.Polynomial.DoubleRoots
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders
public import Mathlib.FieldTheory.Perfect

/-!
# The binary quarter-rate bound on the first input
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial
attribute [local instance] Classical.decEq

/-- A canonical square root for a polynomial supported in even degrees over a
finite field of characteristic two. -/
noncomputable def evenPolynomialSquareRoot
    {F : Type*} [Field F] [Fintype F] [CharP F 2] (P : F[X]) : F[X] :=
  P.sum fun n a ↦ monomial (n / 2) ((frobeniusEquiv F 2).symm a)

/-- The canonical square root squares back to an even-supported polynomial. -/
theorem evenPolynomialSquareRoot_sq
    {F : Type*} [Field F] [Fintype F] [CharP F 2] (P : F[X])
    (heven : ∀ n ∈ P.support, Even n) :
    evenPolynomialSquareRoot P ^ 2 = P := by
  rw [evenPolynomialSquareRoot, ← frobenius_def 2, Polynomial.sum_def, map_sum]
  conv_rhs => rw [P.as_sum_support]
  apply Finset.sum_congr rfl
  intro n hn
  rw [frobenius_def, pow_two, monomial_mul_monomial]
  have hn2 : n / 2 + n / 2 = n := by
    obtain ⟨k, rfl⟩ := heven n hn
    omega
  rw [hn2]
  congr 1
  rw [← pow_two, ← frobeniusEquiv_def]
  exact (frobeniusEquiv F 2).apply_symm_apply (P.coeff n)

/-- Every exponent in the canonical square root comes from halving an
exponent in the original support. -/
theorem evenPolynomialSquareRoot_support
    {F : Type*} [Field F] [Fintype F] [CharP F 2] (P : F[X])
    (n : ℕ) (hn : n ∈ (evenPolynomialSquareRoot P).support) :
    ∃ m ∈ P.support, n = m / 2 := by
  rw [mem_support_iff] at hn
  simp only [evenPolynomialSquareRoot, coeff_sum, coeff_monomial] at hn
  by_contra h
  simp only [not_exists, not_and] at h
  apply hn
  apply Finset.sum_eq_zero
  intro m hm
  simp only [ite_eq_right (Ne.symm (h m hm))]

/-- The polynomial whose square root is the numerator of the binary quarter-rate
first input of Lemma 3.13. -/
noncomputable def binaryQuarterRadicand
    {F : Type*} [Field F] (D : AddSubgroup F) [Fintype D] (β : F) : F[X] :=
  subspacePolynomial D - C ((subspacePolynomial D).coeff 1) * (X - C β)

/-- The canonical numerator used by the binary quarter-rate construction. -/
noncomputable def binaryQuarterNumerator
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) : F[X] :=
  evenPolynomialSquareRoot (binaryQuarterRadicand D β)

/-- The normalized radicand has only even exponents. -/
theorem binaryQuarterRadicand_even_support
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) :
    ∀ n ∈ (binaryQuarterRadicand D β).support, Even n := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    exact Even.zero
  have hncoeff := mem_support_iff.mp hn
  by_cases hn1 : n = 1
  · subst n
    simp [binaryQuarterRadicand] at hncoeff
  have hshape : binaryQuarterRadicand D β = subspacePolynomial D -
      C ((subspacePolynomial D).coeff 1) * X +
        C ((subspacePolynomial D).coeff 1 * β) := by
    simp only [binaryQuarterRadicand]
    rw [mul_sub, ← C_mul]
    ring
  rw [hshape] at hncoeff
  have hLn : (subspacePolynomial D).coeff n ≠ 0 := by
    simpa [coeff_sub, coeff_add, coeff_C_mul, coeff_X, hn1, Ne.symm hn1,
      coeff_C, hn0] using hncoeff
  obtain ⟨i, hi⟩ := subspacePolynomial_support D n (mem_support_iff.mpr hLn)
  subst n
  cases i with
  | zero => simp at hn1
  | succ i => exact ⟨2 ^ i, by rw [pow_succ, Nat.mul_comm, two_mul]⟩

/-- Halving the radicand support leaves only a constant term and powers of
two. -/
theorem binaryQuarterNumerator_support
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (n : ℕ)
    (hn : n ∈ (binaryQuarterNumerator D β).support) :
    n = 0 ∨ ∃ i : ℕ, n = 2 ^ i := by
  obtain ⟨m, hm, rfl⟩ := evenPolynomialSquareRoot_support _ n hn
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmcoeff := mem_support_iff.mp hm
  by_cases hm1 : m = 1
  · subst m
    simp [binaryQuarterRadicand] at hmcoeff
  have hshape : binaryQuarterRadicand D β = subspacePolynomial D -
      C ((subspacePolynomial D).coeff 1) * X +
        C ((subspacePolynomial D).coeff 1 * β) := by
    simp only [binaryQuarterRadicand]
    rw [mul_sub, ← C_mul]
    ring
  rw [hshape] at hmcoeff
  have hLm : (subspacePolynomial D).coeff m ≠ 0 := by
    simpa [coeff_sub, coeff_add, coeff_C_mul, coeff_X, hm1, Ne.symm hm1,
      coeff_C, hm0] using hmcoeff
  obtain ⟨i, hi⟩ := subspacePolynomial_support D m (mem_support_iff.mpr hLm)
  subst m
  cases i with
  | zero => simp at hm1
  | succ i =>
      right
      exact ⟨i, by rw [pow_succ]; omega⟩

/-- A polynomial supported at a constant and powers of two has constant
formal derivative in characteristic two. -/
theorem derivative_eq_C_of_binaryAffineSupport
    {F : Type*} [Field F] [CharP F 2] (P : F[X])
    (hP : ∀ n ∈ P.support, n = 0 ∨ ∃ i : ℕ, n = 2 ^ i) :
    P.derivative = C (P.coeff 1) := by
  ext n
  cases n with
  | zero => simp [coeff_derivative]
  | succ n =>
      rw [coeff_derivative, coeff_C]
      simp only [Nat.succ_ne_zero, ite_false]
      by_cases hc : P.coeff (n + 1 + 1) = 0
      · simp [hc]
      rcases hP (n + 1 + 1) (mem_support_iff.mpr hc) with hzero | ⟨i, hi⟩
      · omega
      have hi0 : i ≠ 0 := by intro h; simp [h] at hi
      have hcast : ((n + 1 + 1 : ℕ) : F) = 0 := by
        rw [hi, Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow hi0]
      simpa only [Nat.cast_add, Nat.cast_one, mul_zero] using
        congrArg (P.coeff (n + 1 + 1) * ·) hcast

/-- The canonical binary quarter-rate numerator has the required square. -/
theorem binaryQuarterNumerator_sq
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) :
    binaryQuarterNumerator D β ^ 2 = binaryQuarterRadicand D β := by
  exact evenPolynomialSquareRoot_sq _ (binaryQuarterRadicand_even_support D β)

/-- The numerator `S` in Lemma 3.13 is the unshifted numerator `R` plus the
unique square root of `λβ`. This is a polynomial identity, so it also holds
at exterior points and does not rely on reduction as a polynomial function. -/
theorem binaryQuarterNumerator_shift
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) :
    binaryQuarterNumerator D β = binaryQuarterNumerator D 0 +
      C ((frobeniusEquiv F 2).symm ((subspacePolynomial D).coeff 1 * β)) := by
  have hroot : ((frobeniusEquiv F 2).symm
      ((subspacePolynomial D).coeff 1 * β)) ^ 2 =
      (subspacePolynomial D).coeff 1 * β := by
    rw [← frobeniusEquiv_def]
    exact (frobeniusEquiv F 2).apply_symm_apply _
  apply CharTwo.sq_injective
  dsimp only
  rw [CharTwo.add_sq, binaryQuarterNumerator_sq, binaryQuarterNumerator_sq,
    ← C_pow, hroot]
  simp only [binaryQuarterRadicand, map_zero, sub_zero]
  rw [mul_sub, ← C_mul]
  ring

/-- The binary normalization in Lemma 3.13 translates the old pole-reduction
challenge set by `-√(λβ)`. This exact set equality keeps the zero challenge and
immediately preserves the number of distinct challenges. -/
theorem badChallenges_binaryQuarterSource_eq_image
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (K T : ℕ) :
    badChallenges (additiveDomain D) K
      (fun x ↦ (binaryQuarterNumerator D β).eval (x : F) * ((x : F) - β)⁻¹)
      (fun x ↦ ((x : F) - β)⁻¹) T =
      (badChallenges (additiveDomain D) K
        (fun x ↦ (binaryQuarterNumerator D 0).eval (x : F) * ((x : F) - β)⁻¹)
        (fun x ↦ ((x : F) - β)⁻¹) T).image
          (fun z ↦ z - (frobeniusEquiv F 2).symm
            ((subspacePolynomial D).coeff 1 * β)) := by
  have hword : (fun x : additiveDomain D ↦
      (binaryQuarterNumerator D β).eval (x : F) * ((x : F) - β)⁻¹) =
      (fun x : additiveDomain D ↦
        (binaryQuarterNumerator D 0).eval (x : F) * ((x : F) - β)⁻¹ +
          (frobeniusEquiv F 2).symm ((subspacePolynomial D).coeff 1 * β) *
            ((x : F) - β)⁻¹) := by
    funext x
    rw [binaryQuarterNumerator_shift, eval_add, eval_C]
    ring
  rw [hword]
  exact badChallenges_add_direction_eq _ _ _ _ _ _

/-- The canonical numerator has constant formal derivative. -/
theorem binaryQuarterNumerator_derivative
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) :
    (binaryQuarterNumerator D β).derivative =
      C ((binaryQuarterNumerator D β).coeff 1) := by
  exact derivative_eq_C_of_binaryAffineSupport _ (binaryQuarterNumerator_support D β)

/-- Core Wronskian bound for a supplied square-root numerator. -/
theorem agreementLE_binaryQuarterSource_of_square
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hKeven : Even K) (hKchar : (K : F) = 0)
    (S : F[X]) (hSsq : S ^ 2 = subspacePolynomial D -
      C ((subspacePolynomial D).coeff 1) * (X - C β))
    (hSdeg : S.natDegree ≤ 2 * K)
    (hS'deg : S.derivative.natDegree ≤ 0) :
    agreementLE (additiveDomain D) K
      (fun x ↦ S.eval (x : F) * ((x : F) - β)⁻¹) (3 * K / 2 - 1) := by
  classical
  let L := subspacePolynomial D
  let lam := L.coeff 1
  have hlam : lam ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  intro h hh
  have hhnat : h.natDegree ≤ K - 1 := by
    by_cases hz : h = 0
    · simp [hz]
    have := (natDegree_lt_iff_degree_lt hz).mpr hh
    omega
  let A := (X - C β) * h
  let P := S - A
  let Q := P ^ 2 - L
  let roots := (additiveDomain D).filter fun x ↦
    h.eval x = S.eval x * (x - β)⁻¹
  rw [agreementCount_eq_card_filter (additiveDomain D)
    (fun x ↦ S.eval x * (x - β)⁻¹) h]
  have hAdeg : A.natDegree ≤ K := by
    calc
      A.natDegree ≤ (X - C β).natDegree + h.natDegree := natDegree_mul_le
      _ ≤ 1 + (K - 1) := Nat.add_le_add (by simp) hhnat
      _ ≤ K := by omega
  have hPdeg : P.natDegree ≤ 2 * K :=
    (natDegree_sub_le _ _).trans (max_le hSdeg (hAdeg.trans (by omega)))
  have hderivA : A.derivative.natDegree ≤ K - 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_derivative]
    by_cases htop : n + 1 = K
    · have hcast : ((n + 1 : ℕ) : F) = 0 := by rw [htop, hKchar]
      have hcast' : (n : F) + 1 = 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hcast
      rw [hcast', mul_zero]
    · have hgt : K < n + 1 := by omega
      have hc : A.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (hAdeg.trans_lt hgt)
      rw [hc, zero_mul]
  have hP'deg : P.derivative.natDegree ≤ K - 2 := by
    simp only [P, derivative_sub]
    exact (natDegree_sub_le _ _).trans (max_le
      (hS'deg.trans (by omega)) hderivA)
  have hQform : Q = A ^ 2 - C lam * (X - C β) := by
    simp only [Q, P, CharTwo.sub_eq_add, CharTwo.add_sq, hSsq, L, lam]
    have htwoP : (2 : F[X]) = 0 := by
      ext n
      simp [CharTwo.two_eq_zero]
    ring_nf
    simp only [htwoP, mul_zero, zero_add]
  have hQdeg : Q.natDegree ≤ 2 * K := by
    rw [hQform]
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hAdeg))
      ((natDegree_mul_le).trans (by simp; omega)))
  have hQ' : Q.derivative = -C lam := by
    rw [hQform]
    rw [derivative_sub, derivative_pow]
    simp [CharTwo.two_eq_zero]
  have hQβ : Q.eval β = 0 := by simp [hQform, A]
  have hPβ : P.eval β ≠ 0 := by
    have hLβ : L.eval β ≠ 0 := by
      rw [show L = subspacePolynomial D from rfl, ne_eq,
        subspacePolynomial_eval_eq_zero_iff]
      exact hβ
    have hSβsq : S.eval β ^ 2 = L.eval β := by
      have he := congrArg (Polynomial.eval β) hSsq
      simpa only [eval_pow, eval_sub, eval_mul, eval_C, eval_X, sub_self,
        mul_zero, sub_zero, L, lam] using he
    have hSβ : S.eval β ≠ 0 := fun hz ↦ hLβ (by simpa [hz] using hSβsq.symm)
    simpa [P, A] using hSβ
  have hroot : ∀ x ∈ roots, P.eval x = 0 ∧ Q.eval x = 0 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxD, hxagree⟩
    have hxD' : x ∈ D := by simpa [additiveDomain] using hxD
    have hxβ : x - β ≠ 0 := sub_ne_zero.mpr (fun he ↦ hβ (he ▸ hxD'))
    have hPzero : P.eval x = 0 := by
      simp only [P, A, eval_sub, eval_mul, eval_X, eval_C]
      field_simp at hxagree
      linear_combination -hxagree
    refine ⟨hPzero, ?_⟩
    simp [Q, hPzero, L, (subspacePolynomial_eval_eq_zero_iff D x).mpr hxD']
  have htwice := twice_card_le_of_wronskian roots P Q lam β hlam hQ' hQβ hPβ
    hroot (2 * K) (K - 2) (2 * K) hPdeg hP'deg hQdeg
  change roots.card ≤ 3 * K / 2 - 1
  obtain ⟨k, hk⟩ := hKeven
  rw [hk] at htwice ⊢
  omega

/-- The canonical binary numerator has degree at most `2K` on a size-`4K`
domain. -/
theorem binaryQuarterNumerator_natDegree_le
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4 * K) :
    (binaryQuarterNumerator D β).natDegree ≤ 2 * K := by
  let L := subspacePolynomial D
  let lam := L.coeff 1
  have hLdeg : L.natDegree = 4 * K := by
    simpa only [L, subspacePolynomial_natDegree] using hcard
  have hcorr : (C lam * (X - C β)).natDegree < L.natDegree := by
    apply lt_of_le_of_lt natDegree_mul_le
    rw [natDegree_C, natDegree_X_sub_C, hLdeg]
    omega
  have hraddeg : (binaryQuarterRadicand D β).natDegree = 4 * K := by
    rw [binaryQuarterRadicand, ← show L = subspacePolynomial D from rfl,
      ← show lam = L.coeff 1 from rfl,
      natDegree_sub_eq_left_of_natDegree_lt hcorr, hLdeg]
  have hsquare := congrArg natDegree (binaryQuarterNumerator_sq D β)
  rw [natDegree_pow, hraddeg] at hsquare
  omega

/-- Lemma 3.13 in the binary quarter-rate case: its first input
has agreement at most `3K/2-1`. -/
theorem agreementLE_binaryQuarterSource
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hpow : ∃ k : ℕ, K = 2 ^ k)
    (hcard : Fintype.card D = 4 * K) :
    agreementLE (additiveDomain D) K
      (fun x ↦ (binaryQuarterNumerator D β).eval (x : F) *
        ((x : F) - β)⁻¹) (3 * K / 2 - 1) := by
  obtain ⟨k, hk⟩ := hpow
  cases k with
  | zero => simp at hk; omega
  | succ k =>
    have hKeven : Even K := by
      refine ⟨2 ^ k, ?_⟩
      rw [hk, pow_succ]
      omega
    have hKchar : (K : F) = 0 := by
      simp [hk, pow_succ, CharTwo.two_eq_zero]
    apply agreementLE_binaryQuarterSource_of_square D β hβ K hK hKeven hKchar
      (binaryQuarterNumerator D β)
    · exact binaryQuarterNumerator_sq D β
    · exact binaryQuarterNumerator_natDegree_le D β K hK hcard
    · rw [binaryQuarterNumerator_derivative]
      simp

end BinaryFieldCounterexamples
