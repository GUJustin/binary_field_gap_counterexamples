/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneFamily
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceFactors
public import BinaryFieldCounterexamples.Polynomial.CompositionDivisibility
/-!
# Factor conversion for actual descended trace polynomials

Literal descent transports scalar-field values and the strict differential
degree bound onto the prescribed hyperplane. Nonconstant composition reflects
divisibility, so the minimum-rank derivative factor also descends. The recovered
sparse support then constructs the actual Frobenius and locator factors over
the original extension field.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- The actual descended polynomial satisfies the differential identity on its prescribed hyperplane. -/
theorem descendedTracePolynomial_differential
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c z v : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n) = c)
    (D : Submodule k B) (hD : Module.finrank k D + 1 = Module.finrank k B)
    (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D) (H : B[X])
    (he : H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z) :
    let L := subspacePolynomial D.toAddSubgroup
    H^(Fintype.card k)-H = -C ((L.coeff 1)⁻¹)*L*H.derivative := by
  dsimp only
  rw [hq]
  apply QuadraticLocatorConversion.differential_identity_on_scalar_submodule p r hr D H
  · intro y hy
    have hmem : y ∈ LinearMap.range (hyperplaneMap (k := k) v) := hrange.symm ▸ hy
    obtain ⟨x, rfl⟩ := hmem
    have hev := congrArg (Polynomial.eval x) he
    rw [eval_comp, hyperplanePolynomial_eval v x hv] at hev
    rw [hev, ← hq]
    exact translatedTracePolynomial_eval_fixed n t a c z x hcard hc
  · have hdeg := congrArg Polynomial.natDegree he
    rw [natDegree_comp, hyperplanePolynomial_natDegree v hv] at hdeg
    have hb := translatedTracePolynomial_degree_comparison n t ht htn a c z hcard
    rw [← hdeg] at hb
    have hcd := hyperplane_card_mul D hD
    rw [Nat.card_eq_fintype_card] at hcd
    rw [← hcd] at hb
    rw [← hq]
    have hmul : (Fintype.card k * H.natDegree) * Fintype.card k <
        (2 * Fintype.card D) * Fintype.card k := by
      simpa only [mul_assoc] using hb
    exact Nat.lt_of_mul_lt_mul_right hmul

/-- A minimum-rank descended trace polynomial admits actual Frobenius and locator factors. -/
theorem descendedTracePolynomial_exists_factors_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c z v : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n) = c)
    (hne : a ≠ 0 ∨ c ≠ 0)
    (hrank : Module.finrank k B - Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical = 2*t)
    (D : Submodule k B) (hD : Module.finrank k D + 1 = Module.finrank k B)
    (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D) (H : B[X])
    (he : H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z)
    (hd : H.derivative.comp (hyperplanePolynomial (k := k) v) =
      (translatedTracePolynomial (k := k) n t a c z).derivative) :
    let L := subspacePolynomial D.toAddSubgroup
    ∃ A P S : B[X], A ≠ 0 ∧ H = A*P ∧ H.derivative = -C (L.coeff 1)*A^(Fintype.card k) ∧
      H = H.derivative*S ∧ P^(Fintype.card k) = L-C (L.coeff 1)*S := by
  dsimp only
  rw [hq]
  apply exists_converted_quadratic_factors p r
  · exact subspacePolynomial_coeff_one_ne_zero _
  · intro hz
    rw [hz, zero_comp] at hd
    exact translatedTracePolynomial_derivative_ne_zero n t ht htn a c z hne hd.symm
  · apply (polynomial_comp_dvd_iff (hyperplanePolynomial (k := k) v) H.derivative H
      (by rw [hyperplanePolynomial_natDegree v hv]; exact Fintype.card_ne_zero)).mp
    rw [he, hd]
    exact translatedTracePolynomial_derivative_dvd_of_exact_rank p r hr hq n t ht htn a c z hcard hc hne hrank
  · intro e hes
    rcases descendedTracePolynomial_derivative_support n t ht htn a c z v hv hcard H hd e hes with hz | ⟨i, hit, _, rfl⟩
    · simp [hz]
    · rw [← hq]
      exact dvd_pow_self _ (by omega)
  · simpa only [← hq] using descendedTracePolynomial_differential p r hr hq n t ht htn a c z v hv hcard hc D hD hrange H he
end BinaryFieldCounterexamples.QuadraticFormTrace
