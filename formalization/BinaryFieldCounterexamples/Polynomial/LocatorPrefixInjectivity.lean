/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.BinarySupport
public import BinaryFieldCounterexamples.Counting.BinarySubspaces
public import BinaryFieldCounterexamples.Agreement.Basic

/-!
# Injectivity of binary locator prefixes

Inside a prescribed size-`2^(m+s)` domain, equal leading locator coefficients
force a difference of degree strictly below `2^(m-s)`. The actual intersection
has at least that many roots, so the subgroups coincide. The nonleading-prefix
form uses monicity to supply the common leading coefficient.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial BinaryLocator

/-- Equal leading binary locator coefficients force a strict sparse degree gap in a nonzero difference. -/
theorem subspacePolynomial_sub_natDegree_lt_of_prefix
    {F : Type*} [Field F] [CharP F 2]
    (U W : AddSubgroup F) [Fintype U] [Fintype W] (m s : ℕ) (hsm : s≤m)
    (hU : Nat.card U=2^m) (hW : Nat.card W=2^m)
    (hprefix : ∀ j≤s, (subspacePolynomial U).coeff (2^(m-j))=
      (subspacePolynomial W).coeff (2^(m-j)))
    (hne : subspacePolynomial U-subspacePolynomial W≠0) :
    (subspacePolynomial U-subspacePolynomial W).natDegree<2^(m-s) := by
  let P := subspacePolynomial U-subspacePolynomial W
  have hsupport : IsBinaryLinearized P :=
    is_binary_linearized_sub _ _ (subspacePolynomial_support U) (subspacePolynomial_support W)
  have hcoeff : P.coeff P.natDegree≠0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  obtain ⟨i,hi⟩ := hsupport P.natDegree (mem_support_iff.mpr hcoeff)
  have hdegU : (subspacePolynomial U).natDegree=2^m := by
    rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hU]
  have hdegW : (subspacePolynomial W).natDegree=2^m := by
    rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hW]
  have hdeg : P.natDegree≤2^m := by
    exact (natDegree_sub_le _ _).trans (by rw [hdegU,hdegW,max_self])
  have him : i≤m := by
    rw [hi] at hdeg
    exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hdeg
  have hilow : i<m-s := by
    by_contra hlow
    have hj : m-i≤s := by omega
    have he := hprefix (m-i) hj
    rw [show m-(m-i)=i by omega] at he
    apply hcoeff
    change (subspacePolynomial U-subspacePolynomial W).coeff P.natDegree=0
    rw [hi,coeff_sub,he,sub_self]
  rw [show (subspacePolynomial U-subspacePolynomial W).natDegree=2^i from hi]
  exact Nat.pow_lt_pow_right (by decide) hilow

/-- Binary subgroups of codimension `s` in the same prescribed domain have at least the expected intersection size. -/
theorem binary_subspace_intersection_card_lower_bound
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D U W : AddSubgroup F) (m s : ℕ) (hsm : s≤m)
    (hD : Nat.card D=2^(m+s)) (hU : Nat.card U=2^m) (hW : Nat.card W=2^m)
    (hUD : U≤D) (hWD : W≤D) : 2^(m-s)≤Nat.card ↥(U⊓W) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have h := binary_subspace_card_mul_le_inf_mul_domain D U W hUD hWD
  rw [hU,hW,hD] at h
  have hp : (2:ℕ)^(m-s)*2^(m+s)=2^m*2^m := by
    rw [←pow_add,←pow_add]
    congr 1
    omega
  rw [←hp] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

/-- The leading `s+1` binary coefficients determine a codimension-`s` subgroup inside a prescribed binary domain. -/
theorem eq_of_subspacePolynomial_prefix_eq
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D U W : AddSubgroup F) [Fintype U] [Fintype W]
    (m s : ℕ) (hsm : s≤m)
    (hD : Nat.card D=2^(m+s)) (hU : Nat.card U=2^m) (hW : Nat.card W=2^m)
    (hUD : U≤D) (hWD : W≤D)
    (hprefix : ∀ j≤s, (subspacePolynomial U).coeff (2^(m-j))=
      (subspacePolynomial W).coeff (2^(m-j))) : U=W := by
  classical
  by_contra hne
  have hpne : subspacePolynomial U-subspacePolynomial W≠0 := by
    intro h
    exact hne (subspacePolynomial_injective U W (sub_eq_zero.mp h))
  have hdeg := subspacePolynomial_sub_natDegree_lt_of_prefix U W m s (by omega) hU hW hprefix hpne
  let S := additiveDomain (U⊓W)
  have hroot : S.filter (fun x => (subspacePolynomial U-subspacePolynomial W).eval x=0)=S := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have hx' : x∈U⊓W := by simpa [S,additiveDomain] using hx
    rw [eval_sub,(subspacePolynomial_eval_eq_zero_iff U x).mpr hx'.1,
      (subspacePolynomial_eval_eq_zero_iff W x).mpr hx'.2,sub_self]
  have hupper := card_filter_eval_eq_zero_le S (subspacePolynomial U-subspacePolynomial W) hpne
  rw [hroot] at hupper
  have hcard : S.card=Nat.card ↥(U⊓W) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rfl
  rw [hcard] at hupper
  have hlower := binary_subspace_intersection_card_lower_bound D U W m s (by omega) hD hU hW hUD hWD
  omega
/-- The `s` nonleading binary coefficients suffice; monicity supplies equality of the leading coefficient. -/
theorem eq_of_subspacePolynomial_nonleading_prefix_eq
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D U W : AddSubgroup F) [Fintype U] [Fintype W]
    (m s : ℕ) (hsm : s≤m)
    (hD : Nat.card D=2^(m+s)) (hU : Nat.card U=2^m) (hW : Nat.card W=2^m)
    (hUD : U≤D) (hWD : W≤D)
    (hprefix : ∀ j, 1≤j → j≤s → (subspacePolynomial U).coeff (2^(m-j))=
      (subspacePolynomial W).coeff (2^(m-j))) : U=W := by
  apply eq_of_subspacePolynomial_prefix_eq D U W m s hsm hD hU hW hUD hWD
  intro j hj
  by_cases hj0 : j=0
  · subst j
    have hdegU : (subspacePolynomial U).natDegree=2^m := by
      rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hU]
    have hdegW : (subspacePolynomial W).natDegree=2^m := by
      rw [subspacePolynomial_natDegree,←Nat.card_eq_fintype_card,hW]
    simpa only [Nat.sub_zero,hdegU,hdegW] using
      (subspacePolynomial_monic U).coeff_natDegree.trans (subspacePolynomial_monic W).coeff_natDegree.symm
  · exact hprefix j (by omega) hj
end BinaryFieldCounterexamples
