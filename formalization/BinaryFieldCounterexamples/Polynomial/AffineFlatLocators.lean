/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.LocatorProducts
public import BinaryFieldCounterexamples.Constructions.Trees.PullbackProperties
/-!
# Locators of affine flats and their unions

Translating the binary subspace locator gives precisely the roots of an affine
flat. Products over a family of flats have the expected root union, monic degree,
and common leading gap. The degree statements count factors, so do not require
a disjointness hypothesis; disjointness is used separately to count supports.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable def affineFlatLocator {F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) : F[X] :=
  (subspacePolynomial A.direction.toAddSubgroup).comp (X-C a)

theorem affineFlatLocator_eval_eq_zero_iff {F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) (ha : a∈A) (x : F) :
    (affineFlatLocator A a).eval x=0 ↔ x∈A := by
  simp only [affineFlatLocator,eval_comp,eval_sub,eval_X,eval_C,subspacePolynomial_eval_eq_zero_iff]
  exact AffineSubspace.vsub_right_mem_direction_iff_mem ha x

theorem affineFlatLocator_natDegree {F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) :
    (affineFlatLocator A a).natDegree=Nat.card A.direction := by
  simp [affineFlatLocator,natDegree_comp,Nat.card_eq_fintype_card]

theorem affineFlatLocator_tail {F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) (m : ℕ)
    (hcard : Nat.card A.direction=2^(m+1)) :
    (affineFlatLocator A a-X^(2^(m+1))).natDegree≤2^m := by
  apply affine_subspacePolynomial_sub_leading_natDegree_le
  rw [←hcard, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

theorem affineFlatLocator_monic {F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (A : AffineSubspace (ZMod 2) F) (a : F) : (affineFlatLocator A a).Monic := by
  exact (subspacePolynomial_monic A.direction.toAddSubgroup).comp (monic_X_sub_C a) (by simp)

noncomputable def affineFlatUnionLocator {ι F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (I : Finset ι) (A : ι → AffineSubspace (ZMod 2) F) (a : ι → F) : F[X] :=
  ∏ i ∈ I, affineFlatLocator (A i) (a i)

theorem affineFlatUnionLocator_eval_eq_zero_iff {ι F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (I : Finset ι) (A : ι → AffineSubspace (ZMod 2) F) (a : ι → F)
    (ha : ∀ i ∈ I, a i∈A i) (x : F) :
    (affineFlatUnionLocator I A a).eval x=0 ↔ ∃ i∈I, x∈A i := by
  simp only [affineFlatUnionLocator,eval_prod,Finset.prod_eq_zero_iff]
  apply exists_congr
  intro i
  exact and_congr_right (fun hi => affineFlatLocator_eval_eq_zero_iff (A i) (a i) (ha i hi) x)

theorem affineFlatUnionLocator_natDegree {ι F : Type*} [Field F] [Fintype F] [Module (ZMod 2) F]
    (I : Finset ι) (A : ι → AffineSubspace (ZMod 2) F) (a : ι → F) (L : ℕ)
    (hcard : ∀ i∈I, Nat.card (A i).direction=L) :
    (affineFlatUnionLocator I A a).natDegree=I.card*L := by
  rw [affineFlatUnionLocator,natDegree_prod_of_monic I (f := fun i => affineFlatLocator (A i) (a i)) (fun i hi => affineFlatLocator_monic (A i) (a i))]
  simp_rw [affineFlatLocator_natDegree]
  rw [Finset.sum_congr rfl hcard]
  simp

theorem affineFlatUnionLocator_tail {ι F : Type*} [Field F] [Fintype F] [CharP F 2] [Module (ZMod 2) F]
    (I : Finset ι) (A : ι → AffineSubspace (ZMod 2) F) (a : ι → F) (m : ℕ)
    (hcard : ∀ i∈I, Nat.card (A i).direction=2^(m+1)) :
    (affineFlatUnionLocator I A a-X^(I.card*2^(m+1))).natDegree≤I.card*2^(m+1)-2^m := by
  apply natDegree_prod_sub_power_le I (fun i => affineFlatLocator (A i) (a i)) _ _
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · intro i hi
    rw [affineFlatLocator_natDegree,hcard i hi]
  · intro i hi
    have h := affineFlatLocator_tail (A i) (a i) m (hcard i hi)
    simpa [pow_succ,Nat.mul_two] using h
end BinaryFieldCounterexamples
