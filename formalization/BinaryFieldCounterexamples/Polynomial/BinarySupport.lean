/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.

The binary tuple recurrence below adapts the binary_span_polynomial
proofs in ArkLib's JohnsonLower.lean at fa14552d40e793f2ea26e65c440306aae0c08a26
(Authors: Alexander Hicks, Aleph). That module exports only its coding-theory
endpoint; this file supplies the bridge for actual subgroup product locators.
-/
module

public import BinaryFieldCounterexamples.Polynomial.SubspacePolynomial
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.NormNum

/-!
# Binary coefficient support of subgroup locators

A product locator of a characteristic-two additive subgroup has nonzero
coefficients only in degrees `2^i`. The proof first establishes the standard
squaring recurrence for a binary tuple, then reindexes the product through a
basis of the subgroup. The tuple product is only a proof device; consumers
continue to use `subspacePolynomial` and its concrete root interface.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open scoped BigOperators

namespace BinaryLocator

/-- A polynomial has binary support when every nonzero coefficient has power-of-two degree. -/
def IsBinaryLinearized {K : Type*} [Field K] (P : Polynomial K) : Prop :=
  ∀ n ∈ P.support, ∃ i : ℕ, n = 2 ^ i

/-- The linear factor belonging to one binary linear combination of a tuple. -/
noncomputable def binary_span_factor
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (c : Fin d → ZMod 2) : Polynomial K :=
  Polynomial.X - Polynomial.C (∑ i : Fin d, c i • v i)

/-- Translation of the variable translates the root of each linear factor. -/
theorem binary_span_factor_comp_sub_c
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (c : Fin d → ZMod 2) (a : K) :
    (binary_span_factor v c).comp (Polynomial.X - Polynomial.C a) =
      Polynomial.X - Polynomial.C ((∑ i : Fin d, c i • v i) + a) := by
  unfold binary_span_factor
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    Polynomial.C_add]
  ring

/-- Appending one tuple entry separates the final binary coefficient. -/
theorem binary_span_factor_snoc
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K)
    (c : Fin d → ZMod 2) (z : ZMod 2) :
    binary_span_factor (Fin.snoc v a) (Fin.snoc c z) =
      Polynomial.X - Polynomial.C ((∑ i : Fin d, c i • v i) + z • a) := by
  unfold binary_span_factor
  congr 2
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The product over all binary combinations of a tuple, with multiplicities when dependent. -/
noncomputable def binary_span_polynomial {K : Type*} [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] {d : ℕ} (v : Fin d → K) : Polynomial K := by
  classical
  exact ∏ a : Fin d → ZMod 2,
    (Polynomial.X - Polynomial.C (∑ i : Fin d, a i • v i))


/-- The tuple product expressed through its individual linear factors. -/
theorem binary_span_polynomial_eq_prod_factor
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) :
    binary_span_polynomial v = ∏ c : Fin d → ZMod 2, binary_span_factor v c := by
  rfl


/-- A binary tuple extension separates into its two final-coordinate fibers. -/
theorem binary_span_polynomial_snoc_reindex
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K) :
    binary_span_polynomial (Fin.snoc v a) =
      ∏ z : ZMod 2, ∏ c : Fin d → ZMod 2,
        binary_span_factor (Fin.snoc v a) (Fin.snoc c z) := by
  classical
  rw [binary_span_polynomial_eq_prod_factor]
  calc
    (∏ c : Fin (d + 1) → ZMod 2,
        binary_span_factor (Fin.snoc v a) c) =
      ∏ p : ZMod 2 × (Fin d → ZMod 2),
        binary_span_factor (Fin.snoc v a) (Fin.snoc p.2 p.1) := by
      exact (Fintype.prod_equiv
        (Fin.snocEquiv (fun _ : Fin (d + 1) => ZMod 2))
        (fun p : ZMod 2 × (Fin d → ZMod 2) =>
          binary_span_factor (Fin.snoc v a) (Fin.snoc p.2 p.1))
        (fun c : Fin (d + 1) → ZMod 2 =>
          binary_span_factor (Fin.snoc v a) c)
        (by intro p; rfl)).symm
    _ = ∏ z : ZMod 2, ∏ c : Fin d → ZMod 2,
        binary_span_factor (Fin.snoc v a) (Fin.snoc c z) := by
      rw [Fintype.prod_prod_type]

/-- Appending a tuple entry multiplies the old product by its translate. -/
theorem binary_span_polynomial_snoc_split
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K) :
    binary_span_polynomial (Fin.snoc v a) =
      binary_span_polynomial v *
        (binary_span_polynomial v).comp (Polynomial.X - Polynomial.C a) := by
  classical
  rw [binary_span_polynomial_snoc_reindex, binary_span_polynomial_eq_prod_factor]
  simp_rw [binary_span_factor_snoc]
  calc
    (∏ z : ZMod 2, ∏ c : Fin d → ZMod 2,
        (Polynomial.X - Polynomial.C
          ((∑ i : Fin d, c i • v i) + z • a))) =
      (∏ c : Fin d → ZMod 2,
        (Polynomial.X - Polynomial.C (∑ i : Fin d, c i • v i))) *
      (∏ c : Fin d → ZMod 2,
        (Polynomial.X - Polynomial.C ((∑ i : Fin d, c i • v i) + a))) := by
      rw [← Fintype.prod_equiv (ZMod.finEquiv 2).toEquiv
        (fun z : Fin 2 => ∏ c : Fin d → ZMod 2,
          (Polynomial.X - Polynomial.C
            ((∑ i : Fin d, c i • v i) + ((ZMod.finEquiv 2) z) • a)))
        (fun z : ZMod 2 => ∏ c : Fin d → ZMod 2,
          (Polynomial.X - Polynomial.C
            ((∑ i : Fin d, c i • v i) + z • a)))
        (by intro z; rfl)]
      rw [Fin.prod_univ_two]
      norm_num
    _ =
      (∏ c : Fin d → ZMod 2, binary_span_factor v c) *
      (∏ c : Fin d → ZMod 2, binary_span_factor v c).comp
        (Polynomial.X - Polynomial.C a) := by
      congr 1
      rw [Polynomial.prod_comp]
      apply Finset.prod_congr rfl
      intro c hc
      rw [binary_span_factor_comp_sub_c]

/-- The empty tuple has one binary combination, giving locator `X`. -/
theorem binary_span_polynomial_zero
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (v : Fin 0 → K) : binary_span_polynomial v = Polynomial.X := by
  unfold binary_span_polynomial
  simp

/-- A binary tuple product is additive as a polynomial translation identity. -/
theorem binary_span_polynomial_translate
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (y : K) :
    (binary_span_polynomial v).comp (Polynomial.X - Polynomial.C y) =
      binary_span_polynomial v -
        Polynomial.C ((binary_span_polynomial v).eval y) := by
  refine Fin.snocInduction (motive := fun {d} v => ∀ y : K,
    (binary_span_polynomial v).comp (Polynomial.X - Polynomial.C y) =
      binary_span_polynomial v - Polynomial.C ((binary_span_polynomial v).eval y))
    ?_ ?_ v y
  · intro y
    rw [binary_span_polynomial_zero]
    simp only [Polynomial.X_comp, Polynomial.eval_X]
  · intro d v a ih y
    have hrec :
        binary_span_polynomial (Fin.snoc v a) =
          (binary_span_polynomial v) ^ 2 -
            Polynomial.C ((binary_span_polynomial v).eval a) *
              binary_span_polynomial v := by
      rw [binary_span_polynomial_snoc_split, ih a]
      ring
    rw [hrec]
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.mul_comp,
      Polynomial.C_comp, ih y, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.C_sub,
      Polynomial.C_pow, Polynomial.C_mul]
    repeat rw [CharTwo.sub_eq_add]
    ring_nf
    rw [CharTwo.two_eq_zero]
    simp only [mul_zero, zero_add]

/-- The binary tuple product satisfies the squaring recurrence. -/
theorem binary_span_polynomial_snoc_recurrence
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K) :
    binary_span_polynomial (Fin.snoc v a) =
      (binary_span_polynomial v) ^ 2 -
        Polynomial.C ((binary_span_polynomial v).eval a) * binary_span_polynomial v := by
  rw [binary_span_polynomial_snoc_split, binary_span_polynomial_translate]
  ring


/-- Scalar multiplication preserves binary coefficient support. -/
theorem is_binary_linearized_c_mul
    {K : Type*} [Field K] (c : K) (P : Polynomial K)
    (hP : IsBinaryLinearized P) :
    IsBinaryLinearized (Polynomial.C c * P) := by
  unfold IsBinaryLinearized
  intro n hn
  rw [Polynomial.mem_support_iff, Polynomial.coeff_C_mul] at hn
  have hp : P.coeff n ≠ 0 := by
    intro hp0
    apply hn
    rw [hp0, mul_zero]
  exact hP n (Polynomial.mem_support_iff.mpr hp)

/-- The polynomial `X` has binary coefficient support. -/
theorem is_binary_linearized_x
    {K : Type*} [Field K] :
    IsBinaryLinearized (Polynomial.X : Polynomial K) := by
  unfold IsBinaryLinearized
  intro n hn
  rw [Polynomial.support_X] at hn
  have hn1 : n = 1 := Finset.mem_singleton.mp hn
  exact ⟨0, by simp [hn1]⟩

/-- Squaring in characteristic two doubles every supported exponent. -/
theorem is_binary_linearized_sq
    {K : Type*} [Field K] [CharP K 2] (P : Polynomial K)
    (hP : IsBinaryLinearized P) :
    IsBinaryLinearized (P ^ 2) := by
  unfold IsBinaryLinearized
  intro n hn
  have hncoeff : (P ^ 2).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  rw [← Polynomial.map_frobenius_expand 2 P, Polynomial.coeff_map,
    Polynomial.coeff_expand (by omega) P n] at hncoeff
  by_cases hd : 2 ∣ n
  · rw [ite_eq_left hd] at hncoeff
    have hpcoeff : P.coeff (n / 2) ≠ 0 := by
      intro hp0
      apply hncoeff
      rw [hp0, map_zero]
    obtain ⟨i, hi⟩ := hP (n / 2) (Polynomial.mem_support_iff.mpr hpcoeff)
    refine ⟨i + 1, ?_⟩
    have heven : Even n := even_iff_two_dvd.mpr hd
    calc
      n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even heven).symm
      _ = 2 * 2 ^ i := by rw [hi]
      _ = 2 ^ (i + 1) := by rw [pow_succ]; omega
  · rw [ite_eq_right hd, map_zero] at hncoeff
    exact False.elim (hncoeff rfl)

/-- Subtraction preserves binary coefficient support. -/
theorem is_binary_linearized_sub
    {K : Type*} [Field K] (P Q : Polynomial K)
    (hP : IsBinaryLinearized P) (hQ : IsBinaryLinearized Q) :
    IsBinaryLinearized (P - Q) := by
  unfold IsBinaryLinearized
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  by_cases hp : P.coeff n = 0
  · have hq : Q.coeff n ≠ 0 := by
      intro hq0
      apply hn
      rw [Polynomial.coeff_sub, hp, hq0, sub_self]
    exact hQ n (Polynomial.mem_support_iff.mpr hq)
  · exact hP n (Polynomial.mem_support_iff.mpr hp)

/-- The tuple recurrence implies power-of-two coefficient support, including dependent tuples. -/
theorem binary_span_polynomial_is_binary_linearized
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) :
    IsBinaryLinearized (binary_span_polynomial v) := by
  refine Fin.snocInduction
    (motive := fun {d} v => IsBinaryLinearized (binary_span_polynomial v))
    ?_ ?_ v
  · rw [binary_span_polynomial_zero]
    exact is_binary_linearized_x
  · intro d v a ih
    rw [binary_span_polynomial_snoc_recurrence]
    exact is_binary_linearized_sub _ _
      (is_binary_linearized_sq _ ih)
      (is_binary_linearized_c_mul _ _ ih)


end BinaryLocator

open BinaryLocator

/-- In characteristic two, only powers of two occur in the subgroup locator.
The subgroup need only be finite; the ambient field need not be finite. -/
theorem subspacePolynomial_support
    {F : Type*} [Field F] [CharP F 2]
    (W : AddSubgroup F) [Fintype W] :
    ∀ n ∈ (subspacePolynomial W).support, ∃ i : ℕ, n = 2 ^ i := by
  classical
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let S : Submodule (ZMod 2) F := AddSubgroup.toZModSubmodule 2 W
  let : Fintype (AddSubgroup.toZModSubmodule 2 W) := inferInstanceAs (Fintype W)
  let b := Module.finBasis (ZMod 2) S
  let v : Fin (Module.finrank (ZMod 2) S) → F := fun i ↦ (b i : F)
  have heq : subspacePolynomial W = binary_span_polynomial v := by
    unfold subspacePolynomial binary_span_polynomial
    apply Fintype.prod_equiv b.equivFun.toEquiv
    intro w
    congr 2
    change (w : F) = ∑ i, b.equivFun w i • (b i : F)
    have hb := b.sum_equivFun w
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
      congrArg (fun z : S ↦ (z : F)) hb.symm
  rw [heq]
  exact binary_span_polynomial_is_binary_linearized v

end BinaryFieldCounterexamples
