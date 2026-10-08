/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.SubspacePolynomial
public import BinaryFieldCounterexamples.Constructions.NearUnit.AdditivePreimages
/-!
# Locator identities for additive preimages

A monic polynomial of the subgroup cardinality which vanishes on the whole
subgroup is its product locator.  This packages the root-count argument needed
to identify additive-preimage locators with Frobenius polynomials.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.NearUnit
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
/-- A monic polynomial of the correct degree vanishing on a finite additive
subgroup is its product locator. -/
theorem subspacePolynomial_eq_of_monic_natDegree_eq
    {F : Type*} [Field F] (D:AddSubgroup F) [Fintype D]
    (P:F[X]) (hP:P.Monic) (hdeg:P.natDegree=Fintype.card D)
    (hroot:∀x:F,x∈D→P.eval x=0) :
    subspacePolynomial D=P := by
  let R:=subspacePolynomial D-P
  have hdegeq:(subspacePolynomial D).degree=P.degree:=by
    rw [degree_eq_natDegree (subspacePolynomial_monic D).ne_zero,
      degree_eq_natDegree hP.ne_zero,subspacePolynomial_natDegree,hdeg]
  have hRdeg:R.degree<(Fintype.card D:WithBot ℕ):=by
    dsimp [R]
    calc
      (subspacePolynomial D-P).degree<P.degree:=
        degree_sub_lt_right hdegeq hP.ne_zero
          (by rw [(subspacePolynomial_monic D).leadingCoeff,hP.leadingCoeff])
      _=(Fintype.card D:WithBot ℕ):=by
        rw [degree_eq_natDegree hP.ne_zero,hdeg]
  have hR:R=0:=by
    by_cases hz:R=0
    · exact hz
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero R
      (f:=fun x:D=>(x:F)) Subtype.val_injective
    · intro x
      dsimp [R]
      rw [eval_sub,(subspacePolynomial_eval_eq_zero_iff D (x:F)).mpr x.property,
        hroot (x:F) x.property,sub_self]
    · exact (natDegree_lt_iff_degree_lt hz).mpr hRdeg
  exact sub_eq_zero.mp hR

/-- The full preimage of an embedded finite field under a monic additive
polynomial has locator `A^|B| + A`. -/
theorem subspacePolynomial_additive_preimage
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (i:B→+*F) (D:AddSubgroup F) [Fintype D] (A:F[X])
    (hA:A.Monic) (hpos:1≤A.natDegree)
    (hcard:Fintype.card D=A.natDegree*Fintype.card B)
    (hmem:∀x:F,x∈D↔∃b:B,A.eval x=i b) :
    subspacePolynomial D=A^(Fintype.card B)+A := by
  have hq:1<Fintype.card B:=Fintype.one_lt_card
  have hnat:A.natDegree<(A^(Fintype.card B)).natDegree:=by
    rw [natDegree_pow]
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hq hpos
  have hdegree:A.degree<(A^(Fintype.card B)).degree:=by
    rw [degree_eq_natDegree hA.ne_zero,
      degree_eq_natDegree (hA.pow (Fintype.card B)).ne_zero]
    exact_mod_cast hnat
  have hmonic:(A^(Fintype.card B)+A).Monic:=
    (hA.pow (Fintype.card B)).add_of_left hdegree
  apply subspacePolynomial_eq_of_monic_natDegree_eq D _ hmonic
  · rw [natDegree_add_eq_left_of_natDegree_lt hnat,natDegree_pow,hcard]
    exact Nat.mul_comm _ _
  · intro x hx
    obtain ⟨b,hb⟩:=(hmem x).mp hx
    simp only [eval_add,eval_pow,hb,←map_pow,FiniteField.pow_card,
      CharTwo.add_self_eq_zero]
end BinaryFieldCounterexamples.NearUnit
