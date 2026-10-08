/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalRoots
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceCoefficients
public import BinaryFieldCounterexamples.Polynomial.PrimePowerSupport
/-!
# The minimum derivative rank of the actual trace family

Coefficient recovery rules out zero derivatives for nonzero parameters. The
literal derivative index gap permits Frobenius root extraction and bounds its
kernel by q^(2n-2t). The derivative evaluation is an actual scalar-linear map,
so rank-nullity gives rank at least 2t on the ambient field of size q^(2n).
The quadratic-form polar identification is supplied separately.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq traceFamilyIndexFintype

/-- The actual derivative has at most q^(2n-2t) distinct roots. -/
theorem traceFamily_derivative_card_roots_le
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) (hne : a ≠ 0 ∨ c ≠ 0) :
    (traceFamilyPolynomial (k:=k) n t a c).derivative.roots.toFinset.card ≤
      (Fintype.card k)^(2*n-2*t) := by
  have he : p^(r*t) = (Fintype.card k)^t := by rw [pow_mul, ← hq]
  apply card_roots_le_of_primePower_support p (r*t) _
    (traceFamily_derivative_ne_zero n t ht htn a c hne)
  · intro e heP
    rw [he]
    exact traceFamily_derivative_support_dvd n t ht htn a c e heP
  · rw [he, ← pow_add]
    have hexp : t+(2*n-2*t)=2*n-t := by omega
    rw [hexp]
    exact traceFamily_derivative_natDegree_le n t ht htn a c

/-- Every concrete derivative-zero set satisfies the same radical-size bound. -/
theorem traceFamily_derivative_zero_set_card_le
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) (hne : a ≠ 0 ∨ c ≠ 0)
    (S : Finset B)
    (hS : ∀ x ∈ S, (traceFamilyPolynomial (k:=k) n t a c).derivative.eval x = 0) :
    S.card ≤ (Fintype.card k)^(2*n-2*t) := by
  have hJ := traceFamily_derivative_ne_zero (k:=k) n t ht htn a c hne
  have hsub : S ⊆ (traceFamilyPolynomial (k:=k) n t a c).derivative.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hJ).mpr (hS x hx))
  exact (Finset.card_le_card hsub).trans
    (traceFamily_derivative_card_roots_le p r hq n t ht htn a c hne)

/-- The literal derivative is supported only in scalar-field Frobenius powers. -/
theorem traceFamily_derivative_q_support
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) :
    FiniteFieldLocator.IsQLinearized (k:=k)
      (traceFamilyPolynomial (k:=k) n t a c).derivative := by
  intro e he
  by_contra h
  push Not at h
  have hmon (z : B) (j : ℕ) : (C z*X^((Fintype.card k)^j)).coeff e = 0 := by
    simp [coeff_C_mul, coeff_X_pow, h j]
  have hz : (traceFamilyPolynomial (k:=k) n t a c).derivative.coeff e = 0 := by
    rw [traceFamilyPolynomial_derivative n t ht htn, coeff_add, finsetSum_coeff,
      hmon c n, add_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_add, hmon, hmon, add_zero]
  exact (mem_support_iff.mp he) hz

/-- Evaluation of the actual derivative as a scalar-linear map. -/
noncomputable def traceFamilyDerivativeLinearMap
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) : B →ₗ[k] B :=
  FiniteFieldLocator.IsQLinearized.evalLinearMap _
    (traceFamily_derivative_q_support n t ht htn a c)

/-- The derivative evaluation map retains its literal polynomial meaning. -/
theorem traceFamilyDerivativeLinearMap_apply
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c x : B) :
    traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c x =
      (traceFamilyPolynomial (k:=k) n t a c).derivative.eval x := by
  rfl

/-- Every nonzero trace parameter has derivative rank at least 2t. -/
theorem traceFamilyDerivativeLinearMap_rank_ge
    {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k = p^r)
    (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (a : TraceFamilyIndex n t → B) (c : B) (hne : a ≠ 0 ∨ c ≠ 0) :
    2*t ≤ Module.finrank k (traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c).range := by
  let J := traceFamilyDerivativeLinearMap (k:=k) n t ht htn a c
  let : Fintype J.ker := Fintype.ofFinite _
  let P := (traceFamilyPolynomial (k:=k) n t a c).derivative
  have hP : P ≠ 0 := traceFamily_derivative_ne_zero n t ht htn a c hne
  have hker : Fintype.card J.ker ≤ P.roots.toFinset.card := by
    let f : J.ker → P.roots.toFinset := fun x => ⟨x.val, by
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hP).mpr
      exact x.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : P.roots.toFinset => (z : B)) h
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hkbound : Fintype.card J.ker ≤ (Fintype.card k)^(2*n-2*t) :=
    hker.trans (traceFamily_derivative_card_roots_le p r hq n t ht htn a c hne)
  rw [Module.card_eq_pow_finrank (K:=k)] at hkbound
  have hkdim := (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp hkbound
  have hdim : Module.finrank k B = 2*n := by
    have he : (Fintype.card k)^(Module.finrank k B) = (Fintype.card k)^(2*n) := by
      rw [← Module.card_eq_pow_finrank (K:=k), hcard]
    exact Nat.pow_right_injective Fintype.one_lt_card he
  have hrank := J.finrank_range_add_finrank_ker
  rw [hdim] at hrank
  change 2*t ≤ Module.finrank k J.range
  omega

end BinaryFieldCounterexamples.QuadraticFormTrace
