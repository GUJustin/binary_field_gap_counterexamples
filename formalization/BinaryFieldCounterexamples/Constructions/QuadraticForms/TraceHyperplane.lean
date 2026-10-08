/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePolar
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Trace normals and maps onto prescribed hyperplanes

Every scalar hyperplane in a finite field extension is the kernel of a nonzero
trace functional. Conjugating the Artin–Schreier map by multiplication produces
a map onto that literal hyperplane with kernel a scalar line. Its representing
polynomial is `X - (v / v^q) X^q`, of exact degree `q`.

This supplies the domain map for quadratic-family descent. Polynomial descent
and rank population are separate subsequent obligations.
-/
@[expose] public section
set_option linter.unusedSectionVars false
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- Every scalar linear functional is an actual trace pairing. -/
theorem trace_functional_surjective : Function.Surjective (Algebra.traceForm k B) := by
  let e := (Module.Free.chooseBasis k B).toDualEquiv
  have hi : Function.Injective (Algebra.traceForm k B) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply (traceForm_nondegenerate k B).1 x
    intro y
    exact LinearMap.congr_fun hx y
  have hs := LinearMap.surjective_of_injective (f := e.symm.toLinearMap.comp (Algebra.traceForm k B)) (e.symm.injective.comp hi)
  intro f
  obtain ⟨x, hx⟩ := hs (e.symm f)
  exact ⟨x, e.symm.injective hx⟩

/-- Every prescribed hyperplane has a nonzero trace normal. -/
theorem hyperplane_trace_normal (D : Submodule k B)
    (hD : Module.finrank k D + 1 = Module.finrank k B) :
    ∃ c : B, c ≠ 0 ∧ D = LinearMap.ker ((Algebra.traceForm k B) c) := by
  have htop : D < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    subst D
    simp only [finrank_top] at hD
    omega)
  obtain ⟨f, hf, hle⟩ := D.exists_le_ker_of_lt_top htop
  obtain ⟨c, hc⟩ := trace_functional_surjective (k := k) (B := B) f
  refine ⟨c, ?_, ?_⟩
  · intro h
    subst c
    simp only [map_zero] at hc
    exact hf hc.symm
  · rw [hc]
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
/-- Scalar Frobenius fixes exactly the embedded scalar field. -/
theorem frobenius_fixed_iff_scalar (x : B) :
    x ^ Fintype.card k = x ↔ ∃ a : k, algebraMap k B a = x := by
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro f
    obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k B).surjective f
    have hp : ∀ n : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic k B ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ, AlgEquiv.mul_apply]
        change (FiniteField.frobeniusAlgEquivOfAlgebraic k B ^ n) (x ^ Fintype.card k) = x
        rw [hx, ih]
    exact hp i.val
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]
/-- The scalar-linear Artin–Schreier difference map. -/
noncomputable def scalarArtinSchreier : B →ₗ[k] B :=
  LinearMap.id - (FiniteField.frobeniusAlgHom k B).toLinearMap

/-- Explicit evaluation of the difference map. -/
theorem scalarArtinSchreier_apply (x : B) :
    scalarArtinSchreier (k := k) x = x - x ^ Fintype.card k := by rfl

/-- The actual kernel is the scalar line through one. -/
theorem scalarArtinSchreier_ker :
    LinearMap.ker (scalarArtinSchreier (k := k) (B := B)) = Submodule.span k {1} := by
  ext x
  simp only [LinearMap.mem_ker, scalarArtinSchreier_apply, sub_eq_zero,
    Submodule.mem_span_singleton, Algebra.smul_def, mul_one]
  exact eq_comm.trans (frobenius_fixed_iff_scalar x)

/-- The actual image is the trace-zero hyperplane. -/
theorem scalarArtinSchreier_range :
    LinearMap.range (scalarArtinSchreier (k := k) (B := B)) =
      LinearMap.ker (Algebra.trace k B) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro y ⟨x, rfl⟩
    change Algebra.trace k B (x - x ^ Fintype.card k) = 0
    rw [map_sub]
    have h := trace_frobenius_power (k := k) 1 x
    simp only [pow_one] at h
    rw [h, sub_self]
  · have h := (scalarArtinSchreier (k := k) (B := B)).finrank_range_add_finrank_ker
    rw [scalarArtinSchreier_ker, finrank_span_singleton (one_ne_zero : (1 : B) ≠ 0)] at h
    have ht : Algebra.trace k B ≠ 0 := by
      intro he
      obtain ⟨x, hx⟩ := Algebra.trace_surjective k B 1
      rw [he, LinearMap.zero_apply] at hx
      exact zero_ne_one hx
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero ht
    omega
/-- The difference map conjugated by multiplication by `v`. -/
noncomputable def hyperplaneMap (v : B) : B →ₗ[k] B :=
  (LinearMap.mulLeft k v).comp ((scalarArtinSchreier (k := k)).comp (LinearMap.mulLeft k v⁻¹))

/-- Explicit evaluation of the conjugated map. -/
theorem hyperplaneMap_apply (v x : B) :
    hyperplaneMap (k := k) v x = v * (v⁻¹ * x - (v⁻¹ * x) ^ Fintype.card k) := by rfl

/-- Its actual image has trace normal `v⁻¹`. -/
theorem hyperplaneMap_range (v : B) (hv : v ≠ 0) :
    LinearMap.range (hyperplaneMap (k := k) v) =
      LinearMap.ker ((Algebra.traceForm k B) v⁻¹) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change Algebra.trace k B (v⁻¹ * (v * _)) = 0
    rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
    have h : scalarArtinSchreier (k := k) (v⁻¹ * x) ∈
        LinearMap.range (scalarArtinSchreier (k := k) (B := B)) := ⟨_, rfl⟩
    rwa [scalarArtinSchreier_range] at h
  · intro hy
    have hh : v⁻¹ * y ∈ LinearMap.range (scalarArtinSchreier (k := k) (B := B)) := by
      rw [scalarArtinSchreier_range]
      exact hy
    obtain ⟨x, hx⟩ := hh
    refine ⟨v * x, ?_⟩
    change v * scalarArtinSchreier (k := k) (v⁻¹ * (v * x)) = y
    rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul, hx,
      ← mul_assoc, mul_inv_cancel₀ hv, one_mul]

/-- Its actual kernel is the scalar line through `v`. -/
theorem hyperplaneMap_ker (v : B) (hv : v ≠ 0) :
    LinearMap.ker (hyperplaneMap (k := k) v) = Submodule.span k {v} := by
  ext x
  simp only [LinearMap.mem_ker, hyperplaneMap_apply, mul_eq_zero, hv, false_or,
    sub_eq_zero, Submodule.mem_span_singleton, Algebra.smul_def]
  rw [eq_comm, frobenius_fixed_iff_scalar]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [ha]
    field_simp
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha]
    field_simp
/-- The concrete polynomial representing the conjugated map. -/
noncomputable def hyperplanePolynomial (v : B) : B[X] :=
  Polynomial.X - Polynomial.C (v / v ^ Fintype.card k) * Polynomial.X ^ Fintype.card k

/-- The concrete polynomial evaluates to the linear map. -/
theorem hyperplanePolynomial_eval (v x : B) (hv : v ≠ 0) :
    (hyperplanePolynomial (k := k) v).eval x = hyperplaneMap (k := k) v x := by
  simp only [hyperplanePolynomial, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, hyperplaneMap_apply,
    mul_pow, inv_pow]
  field_simp

/-- Each prescribed hyperplane is the image of a nonzero-parameter map. -/
theorem exists_hyperplaneMap_range (D : Submodule k B)
    (hD : Module.finrank k D + 1 = Module.finrank k B) :
    ∃ v : B, v ≠ 0 ∧ LinearMap.range (hyperplaneMap (k := k) v) = D := by
  obtain ⟨c, hc, hnormal⟩ := hyperplane_trace_normal D hD
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hyperplaneMap_range _ (inv_ne_zero hc), inv_inv, ← hnormal]
/-- The polynomial has exact degree equal to the scalar-field size. -/
theorem hyperplanePolynomial_natDegree (v : B) (hv : v ≠ 0) :
    (hyperplanePolynomial (k := k) v).natDegree = Fintype.card k := by
  have ha : v / v ^ Fintype.card k ≠ 0 := div_ne_zero hv (pow_ne_zero _ hv)
  unfold hyperplanePolynomial
  rw [natDegree_sub_eq_right_of_natDegree_lt]
  · simp [ha]
  · simpa [natDegree_C_mul, ha] using (Fintype.one_lt_card : 1 < Fintype.card k)
end BinaryFieldCounterexamples.QuadraticFormTrace
