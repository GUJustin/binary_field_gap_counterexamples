/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingRadicals
public import BinaryFieldCounterexamples.Constructions.Gold.Collisions
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound
/-!
# Lemma 5.12: the full square-root source polynomial

The manuscript uses every coefficient of the square root of the domain
locator with its linear term removed. This source is also the numerator of
the quarter-rate pole construction at pole zero. The quotient identity gives
the exact degree of its explaining polynomial without truncating the source.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2]
/-- The full polynomial `R = sqrt(L_D - lambda_0 X)` of Lemma 5.12 and the
proof of Theorem 5.1, including all lower binary coefficients. -/
noncomputable def goldFullSourcePolynomial (D : AddSubgroup B) [Fintype D] : B[X] :=
  binaryQuarterNumerator D 0
/-- The defining square identity of the full source in Lemma 5.12. -/
theorem goldFullSourcePolynomial_sq (D : AddSubgroup B) [Fintype D] :
    goldFullSourcePolynomial D ^ 2 = subspacePolynomial D + C ((subspacePolynomial D).coeff 1)*X := by
  simpa [goldFullSourcePolynomial, binaryQuarterRadicand, sub_eq_add_neg, CharTwo.neg_eq] using
    binaryQuarterNumerator_sq D (0 : B)
/-- Lemma 5.12's quotient construction has the same square identity for the
actual repaired polynomial, before choosing a received word. -/
theorem repairedLocator_sq [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} = 2^k+2^(k-t)) :
    repairedLocator D v A l κ t ^ 2 = subspacePolynomial D +
      subspacePolynomial D / repairedPolynomial D v A l κ := by
  let H := repairedPolynomial D v A l κ
  let U := repairedSquareRoot t H
  have hd := (repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr).1
  have hn : H ≠ 0 := by
    intro hz
    rw [show repairedPolynomial D v A l κ = H from rfl, hz, natDegree_zero] at hd
    have : 0 < (2:ℕ)^k + 2^(k-t) := by positivity
    omega
  have hdiv := (repairedPolynomial_dvd_locator D k hD v A l κ t ht0 ht hM hr hzeros).1
  have hder : H.derivative = U^2 := (repairedSquareRoot_sq t (by omega) H
    (repairedPolynomial_derivative_support D k hD v A l κ t hM)).symm
  have hAS : H^2+H = C ((normalizingRoot D)^2)*subspacePolynomial D*U^2 := by
    rw [show H^2+H=normalizedLocator D*H.derivative from repairedPolynomial_artinSchreier D v A l κ,
      hder, normalizedLocator, ← normalizingRoot_sq]
  exact quotientLocator_sq (normalizingRoot D) U (subspacePolynomial D) H hn hdiv hAS
/-- Lemma 5.12's exact degree `deg(P+R)=T/2`, for the manuscript's full `R`. -/
theorem repairedLocator_fullSource_natDegree [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (l : D →+ ZMod 2) (κ : ZMod 2)
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} = 2^k+2^(k-t)) :
    (repairedLocator D v A l κ t + goldFullSourcePolynomial D).natDegree =
      2^(k-1)-2^(k-t-1) := by
  let H := repairedPolynomial D v A l κ
  let Q := subspacePolynomial D / H
  have hHdeg := (repairedPolynomial_natDegrees D k hD v A l κ t ht0 ht hM hr).1
  have hH : H ≠ 0 := by
    intro hz
    rw [show repairedPolynomial D v A l κ = H from rfl, hz, natDegree_zero] at hHdeg
    have : 0 < (2:ℕ)^k + 2^(k-t) := by positivity
    omega
  have hdiv := (repairedPolynomial_dvd_locator D k hD v A l κ t ht0 ht hM hr hzeros).1
  have hmul : H*Q=subspacePolynomial D := EuclideanDomain.mul_div_cancel' hH hdiv
  have hQ : Q ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hmul
    exact (subspacePolynomial_monic D).ne_zero hmul.symm
  have hdegQ : Q.natDegree=2^k-2^(k-t) := by
    have he := congrArg natDegree hmul
    rw [natDegree_mul hH hQ, show H.natDegree=2^k+2^(k-t) from hHdeg,
      subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card, hD, pow_succ] at he
    omega
  have hsq : (repairedLocator D v A l κ t+goldFullSourcePolynomial D)^2 =
      Q+C ((subspacePolynomial D).coeff 1)*X := by
    rw [CharTwo.add_sq, repairedLocator_sq D k hD v A l κ t ht0 ht hM hr hzeros,
      goldFullSourcePolynomial_sq]
    change (subspacePolynomial D+Q)+(subspacePolynomial D+_) = _
    linear_combination (norm := ring_nf) subspacePolynomial D * (CharTwo.two_eq_zero (R := B[X]))
  have hhalf : 2^k=2^(k-1)*2 := by rw [← pow_succ]; congr 1; omega
  have hsmall : 2^(k-t)<2^(k-1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hpos : 1 < Q.natDegree := by
    rw [hdegQ,hhalf]
    have : 1 ≤ (2:ℕ)^(k-1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hlinear : (C ((subspacePolynomial D).coeff 1)*X).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := C ((subspacePolynomial D).coeff 1)) (q := X))
  have he := congrArg natDegree hsq
  rw [natDegree_pow, natDegree_add_eq_left_of_natDegree_lt (hlinear.trans_lt hpos), hdegQ] at he
  have hunit : 2^(k-t)=2^(k-t-1)*2 := by rw [← pow_succ]; congr 1; omega
  rw [hhalf,hunit] at he
  omega
end BinaryFieldCounterexamples.Gold
