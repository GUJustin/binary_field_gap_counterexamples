/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Parameters
/-!
# Concrete alternating-tensor Gold polynomials

The normalized pair representative cancels its full-domain leading term.
Binary sums therefore interpolate quadratic functional expressions in strict
degree below the prescribed domain size and obey the exact differential
Artin--Schreier identity from the Gold locator lemma.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Squaring shifts each coefficient to twice its exponent in characteristic two. -/
theorem coeff_sq_double {B : Type*} [Field B] [CharP B 2] (P : B[X]) (n : ℕ) : (P ^ 2).coeff (2*n) = P.coeff n ^ 2 := by
  rw [← map_frobenius_expand 2, coeff_map, coeff_expand_mul' (by decide)]
  rfl
/-- The top coefficient of a canonical functional is linear in its Gold parameter. -/
theorem parameterPolynomial_top_coeff (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hD : Nat.card D = 2^(d+1)) (c : parameterDomain D) :
    (parameterPolynomial D c).coeff (2^d) = normalizingRoot D * (c : B) := by
  have hp : (parameterPolynomial D c).natDegree ≤ 2^d := by
    have := (parameterPolynomial_support_and_degree D c).2
    rw [hD, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)] at this
    exact this
  have hlt : 2^d < 2^(d+1) := by
    rw [pow_succ]
    have : 0 < 2^d := by positivity
    omega
  have he := congrArg (fun P : B[X] ↦ P.coeff (2^(d+1)))
    (parameterPolynomial_artinSchreier D c)
  have hc : (subspacePolynomial D).coeff (2^(d+1)) = 1 := by
    rw [← hD, Nat.card_eq_fintype_card, ← subspacePolynomial_natDegree D]
    exact (subspacePolynomial_monic D).coeff_natDegree
  simp only [coeff_add, coeff_C_mul, normalizedLocator] at he
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hlt), add_zero,
    hc, mul_one, pow_succ 2 d, mul_comm (2^d) 2, coeff_sq_double] at he
  apply (frobeniusEquiv B 2).injective
  change (parameterPolynomial D c).coeff (2^d) ^ 2 = (normalizingRoot D * (c : B)) ^ 2
  rw [mul_pow, normalizingRoot_sq, he, mul_comm]

/-- A pair of binary parameters determines the normalized quadratic representative. -/
noncomputable def pairPolynomial (D : AddSubgroup B) [Fintype D]
    (c e : parameterDomain D) : B[X] :=
  parameterPolynomial D c * parameterPolynomial D e +
    C ((c : B) * (e : B)) * normalizedLocator D
/-- The derivative of a pair representative is the explicit alternating expression. -/
theorem pairPolynomial_derivative (D : AddSubgroup B) [Fintype D]
    (c e : parameterDomain D) :
    (pairPolynomial D c e).derivative =
      C ((c : B)^2) * parameterPolynomial D e +
      C ((e : B)^2) * parameterPolynomial D c + C ((c : B)*(e : B)) := by
  simp only [pairPolynomial, derivative_add, derivative_mul, parameterPolynomial_derivative,
    derivative_C, normalizedLocator_derivative, mul_one, zero_mul]
  ring
/-- A quadratic pair obeys the locator differential equation. -/
theorem pairPolynomial_artinSchreier (D : AddSubgroup B) [Fintype D]
    (c e : parameterDomain D) :
    pairPolynomial D c e ^ 2 + pairPolynomial D c e =
      normalizedLocator D * (pairPolynomial D c e).derivative := by
  have hc := parameterPolynomial_artinSchreier D c
  have he := parameterPolynomial_artinSchreier D e
  have hc' : parameterPolynomial D c ^ 2 =
      C ((c : B)^2) * normalizedLocator D + parameterPolynomial D c := by
    rw [← hc, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have he' : parameterPolynomial D e ^ 2 =
      C ((e : B)^2) * normalizedLocator D + parameterPolynomial D e := by
    rw [← he, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [pairPolynomial_derivative]
  simp only [pairPolynomial, CharTwo.add_sq, mul_pow, hc', he', ← C_pow, mul_pow]
  simp only [map_mul]
  linear_combination (norm := ring_nf)
    (normalizedLocator D ^ 2 * C ((c : B)^2) * C ((e : B)^2) +
      parameterPolynomial D c * parameterPolynomial D e) * (CharTwo.two_eq_zero (R := B[X]))
/-- Pair representatives have zero constant term. -/
theorem pairPolynomial_coeff_zero (D : AddSubgroup B) [Fintype D]
    (c e : parameterDomain D) : (pairPolynomial D c e).coeff 0 = 0 := by
  simp [pairPolynomial, parameterPolynomial, functionalPolynomial_coeff_zero,
    normalizedLocator, subspacePolynomial_coeff_zero]
/-- The leading terms cancel, giving the strict degree bound required by the locator lemma. -/
theorem pairPolynomial_degree_lt (D : AddSubgroup B) [Fintype D]
    (d : ℕ) (hD : Nat.card D = 2^(d+1)) (c e : parameterDomain D) :
    (pairPolynomial D c e).degree < Nat.card D := by
  have hp (v : parameterDomain D) : (parameterPolynomial D v).natDegree ≤ 2^d := by
    have hv := (parameterPolynomial_support_and_degree D v).2
    rw [hD, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)] at hv
    exact hv
  have hn : (normalizedLocator D).natDegree ≤ Nat.card D := by
    simpa only [normalizedLocator, subspacePolynomial_natDegree, Nat.card_eq_fintype_card]
      using natDegree_C_mul_le (((subspacePolynomial D).coeff 1)⁻¹) (subspacePolynomial D)
  have hd : (pairPolynomial D c e).natDegree ≤ Nat.card D := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · have h := (natDegree_mul_le (p := parameterPolynomial D c) (q := parameterPolynomial D e)).trans
        (Nat.add_le_add (hp c) (hp e))
      simpa only [hD, pow_succ, Nat.mul_two] using h
    · exact (natDegree_C_mul_le _ _).trans hn
  have hc : (subspacePolynomial D).coeff (Nat.card D) = 1 := by
    rw [Nat.card_eq_fintype_card, ← subspacePolynomial_natDegree D]
    exact (subspacePolynomial_monic D).coeff_natDegree
  have htop : (pairPolynomial D c e).coeff (Nat.card D) = 0 := by
    simp only [pairPolynomial, coeff_add, normalizedLocator, coeff_C_mul, hc, mul_one]
    rw [hD, pow_succ, Nat.mul_two, coeff_mul_add_eq_of_natDegree_le (hp c) (hp e),
      parameterPolynomial_top_coeff D d hD c, parameterPolynomial_top_coeff D d hD e]
    rw [show normalizingRoot D * (c : B) * (normalizingRoot D * (e : B)) =
      (c : B) * (e : B) * normalizingRoot D ^ 2 by ring,
      normalizingRoot_sq, CharTwo.add_self_eq_zero]
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  obtain rfl | hlt := eq_or_lt_of_le hm
  · exact htop
  · exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt hlt)

open scoped BigOperators

/-- Independent coordinates of an alternating binary tensor. -/
abbrev TensorIndex (d : ℕ) := {ij : Fin d × Fin d // ij.1 < ij.2}

/-- An alternating tensor is specified by its binary upper-triangular coordinates. -/
def TensorCoordinates (d : ℕ) := TensorIndex d → ZMod 2

/-- The concrete polynomial of a binary alternating tensor in Gold parameters. -/
noncomputable def tensorPolynomial (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) : B[X] := by
  classical
  exact ∑ ij : TensorIndex d, C (algebraMap (ZMod 2) B (A ij)) *
    pairPolynomial D (v ij.val.1) (v ij.val.2)

/-- Binary scalar multiplication preserves the locator differential identity. -/
theorem artinSchreier_binary_smul {B : Type*} [Field B] [Algebra (ZMod 2) B] (P Λ : B[X])
    (hP : P^2+P=Λ*P.derivative) (a : ZMod 2) :
    (C (algebraMap (ZMod 2) B a)*P)^2+C (algebraMap (ZMod 2) B a)*P =
      Λ*(C (algebraMap (ZMod 2) B a)*P).derivative := by
  rcases binary_eq_zero_or_one a with rfl | rfl
  · simp
  · simpa only [map_one, C_1, one_mul] using hP

/-- Addition preserves the locator differential identity. -/
theorem artinSchreier_add {B : Type*} [Field B] [CharP B 2] (P Q Λ : B[X])
    (hP : P^2+P=Λ*P.derivative) (hQ : Q^2+Q=Λ*Q.derivative) :
    (P+Q)^2+(P+Q)=Λ*(P+Q).derivative := by
  rw [CharTwo.add_sq, derivative_add, mul_add, ← hP, ← hQ]
  ring

/-- Every alternating tensor obeys the exact locator differential equation. -/
theorem tensorPolynomial_artinSchreier (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    tensorPolynomial D v A ^ 2 + tensorPolynomial D v A =
      normalizedLocator D * (tensorPolynomial D v A).derivative := by
  classical
  unfold tensorPolynomial
  have hs (S : Finset (TensorIndex d)) :
      (∑ ij ∈ S, C (algebraMap (ZMod 2) B (A ij)) * pairPolynomial D (v ij.val.1) (v ij.val.2))^2 +
      (∑ ij ∈ S, C (algebraMap (ZMod 2) B (A ij)) * pairPolynomial D (v ij.val.1) (v ij.val.2)) =
      normalizedLocator D * (∑ ij ∈ S, C (algebraMap (ZMod 2) B (A ij)) *
        pairPolynomial D (v ij.val.1) (v ij.val.2)).derivative := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact artinSchreier_add _ _ _
        (artinSchreier_binary_smul _ _ (pairPolynomial_artinSchreier D _ _) _) ih
  exact hs Finset.univ

/-- Tensor representatives keep the strict full-domain degree bound. -/
theorem tensorPolynomial_degree_lt (D : AddSubgroup B) [Fintype D]
    (k : ℕ) (hD : Nat.card D = 2^(k+1))
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    (tensorPolynomial D v A).degree < Nat.card D := by
  classical
  unfold tensorPolynomial
  apply (degree_sum_le _ _).trans_lt
  apply Finset.sup_lt_iff (WithBot.bot_lt_coe _)|>.mpr
  intro ij _
  rcases binary_eq_zero_or_one (A ij) with ha | ha
  · simp [ha]
  · simpa only [ha, map_one, C_1, one_mul] using pairPolynomial_degree_lt D k hD (v ij.val.1) (v ij.val.2)

/-- Tensor representatives have no constant term. -/
theorem tensorPolynomial_coeff_zero (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    (tensorPolynomial D v A).coeff 0 = 0 := by
  classical
  simp only [tensorPolynomial, finsetSum_coeff, coeff_C_mul, pairPolynomial_coeff_zero,
    mul_zero, Finset.sum_const_zero]

/-- The normalized locator vanishes on the original prescribed subgroup. -/
theorem normalizedLocator_eval {B : Type*} [Field B] (D : AddSubgroup B) [Fintype D] (x : D) :
    (normalizedLocator D).eval (x : B) = 0 := by
  simp [normalizedLocator, (subspacePolynomial_eval_eq_zero_iff D (x : B)).mpr x.property]

/-- On the prescribed domain, the pair representative is the product of its binary functionals. -/
theorem pairPolynomial_eval (D : AddSubgroup B) [Fintype D]
    (c e : parameterDomain D) (x : D) :
    (pairPolynomial D c e).eval (x : B) = algebraMap (ZMod 2) B
      (((parameterEquiv D).symm c) x * ((parameterEquiv D).symm e) x) := by
  simp only [pairPolynomial, eval_add, eval_mul, eval_C, normalizedLocator_eval,
    mul_zero, add_zero, parameterPolynomial, functionalPolynomial_eval, map_mul]

/-- Tensor polynomials interpolate the literal binary quadratic expression. -/
theorem tensorPolynomial_eval (D : AddSubgroup B) [Fintype D]
    {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (x : D) :
    (tensorPolynomial D v A).eval (x : B) = algebraMap (ZMod 2) B
      (∑ ij : TensorIndex d, A ij *
        (((parameterEquiv D).symm (v ij.val.1)) x *
          ((parameterEquiv D).symm (v ij.val.2)) x)) := by
  classical
  simp only [tensorPolynomial, eval_finsetSum, eval_mul, eval_C, pairPolynomial_eval,
    map_sum, map_mul]

end BinaryFieldCounterexamples.Gold
