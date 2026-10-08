/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Polynomial.SubspacePolynomial
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Tactic.LinearCombination
public import BinaryFieldCounterexamples.Polynomial.PrimePowerSupport
public import BinaryFieldCounterexamples.Polynomial.LocatorRemainders

/-!
# The quadratic differential identity

A polynomial fixed by prime-power Frobenius on an actual subgroup domain has
the product locator as a divisor of its Frobenius difference. A strict degree
comparison forces the quotient derivative to vanish and yields the literal
differential identity used by locator conversion.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial

/-- The low-degree quotient has zero derivative, giving the exact differential identity. -/
theorem differential_identity_of_divisibility
    {F : Type*} [Field F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (L G : F[X]) (lam : F) (hlam : lam ≠ 0)
    (hL : L ≠ 0) (hLdegree : 0 < L.natDegree)
    (hderiv : L.derivative = C lam)
    (hdiv : L ∣ G^(p^r)-G)
    (hdegree : p^r*G.natDegree < 2*L.natDegree) :
    G^(p^r)-G = -C (lam⁻¹)*L*G.derivative := by
  obtain ⟨B, hB⟩ := hdiv
  have hb : 2 ≤ p^r := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow (by omega) p)
  have hbchar : ((p^r : ℕ) : F) = 0 := by simp [show r ≠ 0 by omega]
  have hGsmall : G.natDegree < L.natDegree := by nlinarith
  have hBsmall : B.natDegree < L.natDegree := by
    by_cases hz : B = 0
    · simpa [hz] using hLdegree
    have hd : (G^(p^r)-G).natDegree ≤ p^r*G.natDegree := by
      apply (natDegree_sub_le _ _).trans
      rw [natDegree_pow]
      exact max_le le_rfl (by nlinarith)
    rw [hB, natDegree_mul hL hz] at hd
    omega
  have he := congrArg Polynomial.derivative hB
  simp only [derivative_sub, derivative_pow, hbchar, C_0, zero_mul, zero_sub,
    derivative_mul, hderiv] at he
  have hp : L*B.derivative = -G.derivative-C lam*B := by linear_combination -he
  have hsmall : (-G.derivative-C lam*B).natDegree < L.natDegree := by
    apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · rw [natDegree_neg]
      exact (natDegree_derivative_le G).trans_lt ((Nat.sub_le _ _).trans_lt hGsmall)
    · exact natDegree_mul_le.trans_lt (by simpa using hBsmall)
  have hBderiv : B.derivative = 0 := by
    by_contra hn
    rw [← hp, natDegree_mul hL hn] at hsmall
    omega
  rw [hBderiv, mul_zero, add_zero] at he
  rw [hB]
  calc
    L*B = C (lam⁻¹)*(L*(C lam*B)) := by
      simp only [mul_left_comm L (C lam), ← mul_assoc, ← C_mul]
      simp [hlam]
    _ = -C (lam⁻¹)*L*G.derivative := by rw [← he]; ring

/-- Vanishing on every subgroup element implies divisibility by its actual product locator. -/
theorem subspacePolynomial_dvd_of_eval_zero
    {F : Type*} [Field F] (D : AddSubgroup F) [Fintype D] (P : F[X])
    (hzero : ∀ x ∈ D, P.eval x = 0) : subspacePolynomial D ∣ P := by
  classical
  unfold subspacePolynomial
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact pairwise_coprime_X_sub_C (fun x y h => Subtype.ext h) hab
  · intro x _
    exact dvd_iff_isRoot.mpr (hzero x x.property)

/-- Frobenius-fixed values and the degree bound imply the differential identity on an actual domain. -/
theorem differential_identity_of_fixed_values
    {F : Type*} [Field F] (p r : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 1 ≤ r) (D : AddSubgroup F) [Fintype D] (G : F[X]) (lam : F)
    (hlam : lam ≠ 0) (hderiv : (subspacePolynomial D).derivative = C lam)
    (hfixed : ∀ x ∈ D, G.eval x ^ (p^r) = G.eval x)
    (hdegree : p^r*G.natDegree < 2*Fintype.card D) :
    G^(p^r)-G = -C (lam⁻¹)*subspacePolynomial D*G.derivative := by
  apply differential_identity_of_divisibility p r hr (subspacePolynomial D) G lam hlam
    (subspacePolynomial_monic D).ne_zero
  · rw [subspacePolynomial_natDegree]
    exact Fintype.card_pos
  · exact hderiv
  · apply subspacePolynomial_dvd_of_eval_zero
    intro x hx
    simp only [eval_sub, eval_pow]
    exact sub_eq_zero.mpr (hfixed x hx)
  · simpa only [subspacePolynomial_natDegree] using hdegree

/-- An actual scalar-submodule supplies its constant nonzero derivative, so
Frobenius-fixed values and the degree estimate suffice for conversion. -/
theorem differential_identity_on_scalar_submodule
    {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (p r : ℕ) [Fact p.Prime] [CharP F p] (hr : 1 ≤ r)
    (D : Submodule k F) [Fintype D] (G : F[X])
    (hfixed : ∀ x ∈ D, G.eval x ^ (p^r) = G.eval x)
    (hdegree : p^r*G.natDegree < 2*Fintype.card D) :
    G^(p^r)-G = -C (((subspacePolynomial D.toAddSubgroup).coeff 1)⁻¹)*
      subspacePolynomial D.toAddSubgroup*G.derivative := by
  exact differential_identity_of_fixed_values p r hr D.toAddSubgroup G _
    (subspacePolynomial_coeff_one_ne_zero _)
    (FiniteFieldLocator.subspacePolynomial_derivative D) hfixed hdegree

end BinaryFieldCounterexamples.QuadraticLocatorConversion
