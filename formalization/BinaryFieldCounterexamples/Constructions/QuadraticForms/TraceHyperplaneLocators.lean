/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneDegree
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceLocators
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperplaneFiberCount
/-!
# Actual hyperplane locators with strict degree and exact agreement

A minimum-rank translated trace polynomial descended onto a prescribed
hyperplane produces literal conversion factors and a common numerator plus a
strict-degree correction. The actual fiber cardinality divides its ambient
zero count by q, giving the exact elliptic agreement count on the hyperplane.
No population or hypothetical locator family is assumed.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Construct actual hyperplane conversion factors and a strict-degree correction, with agreement equal to the descended zero count. -/
theorem descendedTracePolynomial_exists_locator_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t < n)
    (a : TraceFamilyIndex n t → B) (c z v β : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n) = c)
    (hne : a ≠ 0 ∨ c ≠ 0)
    (hrank : Module.finrank k B - Module.finrank k (traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical = 2*t)
    (D : Submodule k B) (hD : Module.finrank k D + 1 = Module.finrank k B)
    (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D) (H : B[X])
    (he : H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z)
    (hd : H.derivative.comp (hyperplanePolynomial (k := k) v) =
      (translatedTracePolynomial (k := k) n t a c z).derivative) :
    let L := subspacePolynomial D.toAddSubgroup
    let Df := Finset.univ.filter (fun x : B => x ∈ D)
    ∃ A P U : B[X], A ≠ 0 ∧ H=A*P ∧
      A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
      P=primePowerQuarterNumerator p r L β+U ∧ U.degree<(Fintype.card k)^(2*n-3) ∧
      A.natDegree=(Fintype.card k)^(2*n-t-2) ∧
      agreementCount Df (fun x => (primePowerQuarterNumerator p r L β).eval x.val) (-U)=
        (Df.filter (fun x => H.eval x=0)).card := by
  dsimp only
  let L := subspacePolynomial D.toAddSubgroup
  let Df := Finset.univ.filter (fun x : B => x ∈ D)
  obtain ⟨A,P,S,hA,hH,hJ,hS,hP⟩ := descendedTracePolynomial_exists_factors_of_exact_rank
    p r hr hq n t ht (by omega) a c z v hv hcard hc hne hrank D hD hrange H he hd
  have hlam : L.coeff 1 ≠ 0 := subspacePolynomial_coeff_one_ne_zero _
  obtain ⟨hHd,hJd⟩ := descendedTracePolynomial_degrees_of_exact_rank p r hr hq n t ht htn a c z v hv hcard hc hne hrank H he hd
  have he1 : 2*n-1-1=2*n-2 := by omega
  have he2 : 2*n-1-t-1=2*n-t-2 := by omega
  have he3 : 2*n-1-t=2*n-t-1 := by omega
  obtain ⟨hdA,hdP,hdS⟩ := quadratic_factor_degrees (Fintype.card k) (2*n-1) t Fintype.one_lt_card
    ht (by omega) H H.derivative A P S (L.coeff 1) hlam hA hH hJ hS
    (by simpa only [he1, he2] using hHd) (by simpa only [he3] using hJd)
  have hdiff := descendedTracePolynomial_differential p r hr hq n t ht (by omega) a c z v hv hcard hc D hD hrange H he
  have hconv : A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P :=
    QuadraticLocatorConversion.conversion_identity H A P L (L.coeff 1) (Fintype.card k)
      Fintype.one_lt_card hlam hA hH hJ hdiff
  have hsupp : ∀ e ∈ L.support, ∃ i : ℕ, e=(p^r)^i := by
    intro e hes
    obtain ⟨i, hi⟩ := FiniteFieldLocator.subspacePolynomial_q_support D e hes
    exact ⟨i, by simpa only [hq] using hi⟩
  have hSlt : S.natDegree < p^r*(Fintype.card k)^(2*n-3) := by
    rw [hdS, he1, he2, ← hq]
    have hpw : (Fintype.card k)*(Fintype.card k)^(2*n-3)=(Fintype.card k)^(2*n-2) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpw]
    apply Nat.sub_lt (pow_pos Fintype.card_pos _)
    exact Nat.mul_pos (by have := Fintype.one_lt_card (α := k); omega) (pow_pos Fintype.card_pos _)
  obtain ⟨U,hU,hdU⟩ := converted_quadratic_strict_correction p r hr P S L β
    ((Fintype.card k)^(2*n-3)) (pow_pos Fintype.card_pos _) hsupp (by simpa only [hq] using hP) hSlt
  refine ⟨A,P,U,hA,hH,hconv,hU,hdU,?_,?_⟩
  · simpa only [he2] using hdA
  · rw [agreementCount_eq_card_filter Df (fun x : B => (primePowerQuarterNumerator p r L β).eval x) (-U)]
    congr 1
    ext x
    simp only [Df, Finset.mem_filter, Finset.mem_univ, true_and, eval_neg]
    have hz := QuadraticLocatorConversion.converted_isRoot_iff H A P L (Fintype.card k)
      Fintype.one_lt_card hH hconv x
    change P.eval x=0 ↔ H.eval x=0 at hz
    rw [← hz]
    simp only [hU, eval_add]
    constructor
    · rintro ⟨hx, hh⟩
      exact ⟨hx, by linear_combination -hh⟩
    · rintro ⟨hx, hh⟩
      exact ⟨hx, by linear_combination -hh⟩
/-- The actual descended zero count is the ambient elliptic count divided by q. -/
theorem descendedTracePolynomial_zero_card_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t < n)
    (a : TraceFamilyIndex n t → B) (c z v : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n) = c)
    (hne : a ≠ 0 ∨ c ≠ 0)
    (hrank : Module.finrank k B - Module.finrank k (traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical = 2*t)
    (D : Submodule k B) (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D) (H : B[X])
    (he : H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z) :
    ((Finset.univ.filter (fun x : B => x ∈ D)).filter (fun x => H.eval x=0)).card =
      (Fintype.card k)^(2*n-2)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-2) := by
  have hcount : Nat.card {y : D // H.eval y.val=0} =
      ((Finset.univ.filter (fun x : B => x ∈ D)).filter (fun x => H.eval x=0)).card := by
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : B => x ∈ D) (fun x => H.eval x=0)),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.filter_filter]
  have hf := hyperplanePolynomial_zero_natCard v hv D hrange H
  rw [he, hcount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    translatedTracePolynomial_zero_card_of_exact_rank p r hr hq n t ht (by omega) a c z hcard hc hne hrank] at hf
  have he1 : (Fintype.card k)*(Fintype.card k)^(2*n-2)=(Fintype.card k)^(2*n-1) := by
    rw [← pow_succ']; congr 1; omega
  have he2 : (Fintype.card k)*(Fintype.card k)^(2*n-t-2)=(Fintype.card k)^(2*n-t-1) := by
    rw [← pow_succ']; congr 1; omega
  apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := k))
  rw [← hf, Nat.mul_sub, ← mul_assoc, mul_comm (Fintype.card k) (Fintype.card k-1), mul_assoc, he1, he2]

/-- Construct an actual hyperplane locator and strict-degree explaining polynomial with the exact required agreement count. -/
theorem descendedTracePolynomial_exists_locator_exact_agreement
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1 ≤ r) (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t < n)
    (a : TraceFamilyIndex n t → B) (c z v β : B) (hv : v ≠ 0)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n) = c)
    (hne : a ≠ 0 ∨ c ≠ 0)
    (hrank : Module.finrank k B - Module.finrank k (traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical = 2*t)
    (D : Submodule k B) (hD : Module.finrank k D + 1 = Module.finrank k B)
    (hrange : LinearMap.range (hyperplaneMap (k := k) v) = D) (H : B[X])
    (he : H.comp (hyperplanePolynomial (k := k) v) = translatedTracePolynomial (k := k) n t a c z)
    (hd : H.derivative.comp (hyperplanePolynomial (k := k) v) =
      (translatedTracePolynomial (k := k) n t a c z).derivative) :
    let L := subspacePolynomial D.toAddSubgroup
    let Df := Finset.univ.filter (fun x : B => x ∈ D)
    ∃ A P U : B[X], A ≠ 0 ∧ H=A*P ∧
      A^(Fintype.card k-1)*(P^(Fintype.card k)-L)=P ∧
      P=primePowerQuarterNumerator p r L β+U ∧ U.degree<(Fintype.card k)^(2*n-3) ∧
      A.natDegree=(Fintype.card k)^(2*n-t-2) ∧
      agreementCount Df (fun x => (primePowerQuarterNumerator p r L β).eval x.val) (-U)=
        (Fintype.card k)^(2*n-2)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-2) := by
  obtain ⟨A,P,U,hA,hH,hconv,hU,hdU,hdA,hagr⟩ := descendedTracePolynomial_exists_locator_of_exact_rank
    p r hr hq n t ht htn a c z v β hv hcard hc hne hrank D hD hrange H he hd
  refine ⟨A,P,U,hA,hH,hconv,hU,hdU,hdA,?_⟩
  rw [hagr]
  exact descendedTracePolynomial_zero_card_of_exact_rank p r hr hq n t ht htn a c z v hv
    hcard hc hne hrank D hrange H he
end BinaryFieldCounterexamples.QuadraticFormTrace
