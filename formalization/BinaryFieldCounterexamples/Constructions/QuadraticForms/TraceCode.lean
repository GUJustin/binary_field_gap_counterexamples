/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ParameterCount

/-!
# The actual additive quadratic trace code

The half-fixed coefficients form a scalar subspace. Literal trace polynomials
are linear in every parameter, so the packaged quadratic forms are the image
of an injective linear map. Its actual finite range has the exact dimension,
cardinality and quadratic-radical minimum-distance bound required for the
population argument. No rank distribution or character moment is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
open FiniteFieldLocator
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Algebra k B]

/-- The full cyclic block is additive in its literal coefficient. -/
theorem cyclicTracePolynomial_add (m i : ℕ) (a b : B) :
    cyclicTracePolynomial (k:=k) m i (a+b) =
      cyclicTracePolynomial (k:=k) m i a + cyclicTracePolynomial (k:=k) m i b := by
  simp only [cyclicTracePolynomial, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have he := (qPowerLinearMap (k:=k) (K:=B) j).map_add a b
  simp only [qPowerLinearMap_apply] at he
  rw [he, map_add, add_mul]

/-- The half-trace block is additive in its literal coefficient. -/
theorem halfTracePolynomial_add (n : ℕ) (a b : B) :
    halfTracePolynomial (k:=k) n (a+b) =
      halfTracePolynomial (k:=k) n a + halfTracePolynomial (k:=k) n b := by
  simp only [halfTracePolynomial, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have he := (qPowerLinearMap (k:=k) (K:=B) j).map_add a b
  simp only [qPowerLinearMap_apply] at he
  rw [he, map_add, add_mul]

/-- The full cyclic block is scalar-linear in its coefficient. -/
theorem cyclicTracePolynomial_smul (m i : ℕ) (s : k) (a : B) :
    cyclicTracePolynomial (k:=k) m i (s • a) = s • cyclicTracePolynomial (k:=k) m i a := by
  simp only [cyclicTracePolynomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he := (qPowerLinearMap (k:=k) (K:=B) j).map_smul s a
  simp only [qPowerLinearMap_apply] at he
  rw [he]
  ext e
  simp only [coeff_C_mul, coeff_smul, coeff_X_pow]
  split_ifs <;> simp

/-- The half-trace block is scalar-linear in its coefficient. -/
theorem halfTracePolynomial_smul (n : ℕ) (s : k) (a : B) :
    halfTracePolynomial (k:=k) n (s • a) = s • halfTracePolynomial (k:=k) n a := by
  simp only [halfTracePolynomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he := (qPowerLinearMap (k:=k) (K:=B) j).map_smul s a
  simp only [qPowerLinearMap_apply] at he
  rw [he]
  ext e
  simp only [coeff_C_mul, coeff_smul, coeff_X_pow]
  split_ifs <;> simp

/-- The whole polynomial family is additive in its actual parameters. -/
theorem traceFamilyPolynomial_add (n t : ℕ) (a b : TraceFamilyIndex n t → B) (c d : B) :
    traceFamilyPolynomial (k:=k) n t (a+b) (c+d) =
      traceFamilyPolynomial (k:=k) n t a c + traceFamilyPolynomial (k:=k) n t b d := by
  simp only [traceFamilyPolynomial, Pi.add_apply, cyclicTracePolynomial_add,
    halfTracePolynomial_add, Finset.sum_add_distrib]
  ring

/-- The whole polynomial family is scalar-linear in its actual parameters. -/
theorem traceFamilyPolynomial_smul (n t : ℕ) (s : k) (a : TraceFamilyIndex n t → B) (c : B) :
    traceFamilyPolynomial (k:=k) n t (s • a) (s • c) =
      s • traceFamilyPolynomial (k:=k) n t a c := by
  simp only [traceFamilyPolynomial, Pi.smul_apply, cyclicTracePolynomial_smul,
    halfTracePolynomial_smul, Finset.smul_sum, smul_add]

/-- The actual scalar subspace of middle-Frobenius-fixed coefficients. -/
noncomputable def halfCoefficientSpace (n : ℕ) : Submodule k B :=
  LinearMap.ker (qPowerLinearMap (k:=k) n - LinearMap.id)

/-- Membership retains the literal middle coefficient equation. -/
theorem mem_halfCoefficientSpace (n : ℕ) (c : B) :
    c ∈ halfCoefficientSpace (k:=k) n ↔ c^((Fintype.card k)^n)=c := by
  simp [halfCoefficientSpace, LinearMap.mem_ker, qPowerLinearMap_apply, sub_eq_zero]

variable [Fintype B]

/-- Addition of parameters adds the actual packaged quadratic forms. -/
theorem traceFamilyQuadraticForm_add (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a b : TraceFamilyIndex n t → B) (c d : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hd : d^((Fintype.card k)^n)=d)
    (hcd : (c+d)^((Fintype.card k)^n)=c+d) :
    traceFamilyQuadraticForm n t ht htn (a+b) (c+d) hcard hcd =
      traceFamilyQuadraticForm n t ht htn a c hcard hc +
      traceFamilyQuadraticForm n t ht htn b d hcard hd := by
  ext x
  apply (algebraMap k B).injective
  simp only [_root_.add_apply, map_add, algebraMap_traceFamilyQuadraticForm]
  rw [traceFamilyPolynomial_add, eval_add]

/-- Scaling parameters scales the actual packaged quadratic forms. -/
theorem traceFamilyQuadraticForm_smul (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (s : k) (a : TraceFamilyIndex n t → B) (c : B)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hsc : (s • c)^((Fintype.card k)^n)=s • c) :
    traceFamilyQuadraticForm n t ht htn (s • a) (s • c) hcard hsc =
      s • traceFamilyQuadraticForm n t ht htn a c hcard hc := by
  ext x
  apply (algebraMap k B).injective
  simp only [_root_.smul_apply, smul_eq_mul, map_mul, algebraMap_traceFamilyQuadraticForm]
  rw [traceFamilyPolynomial_smul, eval_smul, Algebra.smul_def]

/-- The concrete scalar-linear parameterization of the quadratic trace family. -/
noncomputable def traceFamilyParameterLinearMap (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    ((TraceFamilyIndex n t → B) × halfCoefficientSpace (k:=k) (B:=B) n) →ₗ[k] QuadraticForm k B := by
  exact
    { toFun := fun u => traceFamilyQuadraticForm n t ht htn u.1 u.2.val hcard
        ((mem_halfCoefficientSpace n u.2.val).mp u.2.property)
      map_add' := fun u v => traceFamilyQuadraticForm_add n t ht htn u.1 v.1 u.2.val v.2.val
        hcard _ _ _
      map_smul' := fun s u => traceFamilyQuadraticForm_smul n t ht htn s u.1 u.2.val hcard _ _ }

/-- Actual parameter recovery makes the linear parameterization injective. -/
theorem traceFamilyParameterLinearMap_injective (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    Function.Injective (traceFamilyParameterLinearMap (k:=k) (B:=B) n t ht htn hcard) := by
  intro u v huv
  obtain ⟨ha,hc⟩ := traceFamily_parameters_eq_of_quadraticForm_eq n t ht htn u.1 v.1
    u.2.val v.2.val hcard _ _ huv
  exact Prod.ext ha (Subtype.ext hc)

/-- The actual scalar subspace of quadratic forms supplied by the trace family. -/
noncomputable def traceQuadraticCode (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) : Submodule k (QuadraticForm k B) :=
  (traceFamilyParameterLinearMap n t ht htn hcard).range

/-- The linear code and the previously counted finite family have the same elements. -/
theorem mem_traceQuadraticCode_iff (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (Q : QuadraticForm k B) :
    Q ∈ traceQuadraticCode n t ht htn hcard ↔ Q ∈ traceQuadraticFamily n t ht htn hcard := by
  simp only [traceQuadraticCode, LinearMap.mem_range, traceQuadraticFamily,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨u.1, ⟨u.2.val, (mem_halfCoefficientSpace n u.2.val).mp u.2.property⟩⟩, ?_⟩
    exact hu
  · rintro ⟨u, hu⟩
    refine ⟨⟨u.1, ⟨u.2.val, (mem_halfCoefficientSpace n u.2.val).mpr u.2.property⟩⟩, ?_⟩
    exact hu

/-- The actual additive quadratic code has the prescribed cardinality. -/
theorem traceQuadraticCode_natCard (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    Nat.card (traceQuadraticCode (k:=k) (B:=B) n t ht htn hcard) =
      (Fintype.card k)^(2*n*(n-t)+n) := by
  let e : traceQuadraticCode n t ht htn hcard ≃ traceQuadraticFamily n t ht htn hcard :=
    { toFun := fun Q => ⟨Q.val, (mem_traceQuadraticCode_iff n t ht htn hcard Q.val).mp Q.property⟩
      invFun := fun Q => ⟨Q.val, (mem_traceQuadraticCode_iff n t ht htn hcard Q.val).mpr Q.property⟩
      left_inv := by intro Q; rfl
      right_inv := by intro Q; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact traceQuadraticFamily_card n t ht htn hcard

/-- The actual additive quadratic code has the prescribed scalar dimension. -/
theorem traceQuadraticCode_finrank (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    Module.finrank k (traceQuadraticCode (k:=k) (B:=B) n t ht htn hcard) =
      2*n*(n-t)+n := by
  let : Fintype (QuadraticForm k B) := Fintype.ofInjective
    (fun Q : QuadraticForm k B => (Q : B → k)) DFunLike.coe_injective
  have hh := Module.natCard_eq_pow_finrank (K:=k)
    (V:=traceQuadraticCode (k:=k) (B:=B) n t ht htn hcard)
  rw [traceQuadraticCode_natCard n t ht htn hcard, Nat.card_eq_fintype_card] at hh
  exact (Nat.pow_right_injective Fintype.one_lt_card hh).symm

/-- Every nonzero code element has quadratic-radical codimension at least twice the start index. -/
theorem traceQuadraticCode_minimum_rank (p r : ℕ) [Fact p.Prime] [CharP B p]
    (hq : Fintype.card k=p^r) (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (Q : QuadraticForm k B)
    (hQ : Q ∈ traceQuadraticCode n t ht htn hcard) (hne : Q ≠ 0) :
    2*t ≤ Module.finrank k B - Module.finrank k Q.radical := by
  obtain ⟨u, rfl⟩ := hQ
  have hu : u.1 ≠ 0 ∨ u.2.val ≠ 0 := by
    by_contra h
    push Not at h
    have he : u = 0 := Prod.ext h.1 (Subtype.ext h.2)
    apply hne
    change traceFamilyParameterLinearMap n t ht htn hcard u = 0
    rw [he, map_zero]
  exact traceFamilyQuadraticForm_radical_codim_ge p r hq n t ht htn u.1 u.2.val
    hcard ((mem_halfCoefficientSpace n u.2.val).mp u.2.property) hu

/-- The code cardinality matches the normalization of the two weighted population moments. -/
theorem traceQuadraticCode_natCard_eq_moment_scale (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) :
    Nat.card (traceQuadraticCode (k:=k) (B:=B) n t ht htn hcard) =
      (Fintype.card k)^((2*n+1)*(n-t))*(Fintype.card k)^t := by
  rw [traceQuadraticCode_natCard, ← pow_add]
  congr 1
  have he := Nat.sub_add_cancel htn
  linarith

/-- Distinct actual code elements differ by a form of quadratic rank at least twice the start index. -/
theorem traceQuadraticCode_minimum_distance (p r : ℕ) [Fact p.Prime] [CharP B p]
    (hq : Fintype.card k=p^r) (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n)) (Q R : QuadraticForm k B)
    (hQ : Q ∈ traceQuadraticCode n t ht htn hcard)
    (hR : R ∈ traceQuadraticCode n t ht htn hcard) (hne : Q ≠ R) :
    2*t ≤ Module.finrank k B - Module.finrank k (Q-R).radical := by
  exact traceQuadraticCode_minimum_rank p r hq n t ht htn hcard (Q-R)
    ((traceQuadraticCode n t ht htn hcard).sub_mem hQ hR) (sub_ne_zero.mpr hne)

end BinaryFieldCounterexamples.QuadraticFormTrace
