/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.MomentPopulation
public import BinaryFieldCounterexamples.Constructions.Gold.PairWitnesses
/-!
# Gold polynomials on Longfellow's embedded affine space

Every affine binary 11-space in a field of size `2^16` carries 5,843,376
polynomials with at least 768 roots each. Their corrections to a common
polynomial have degree exactly 384. Both translation and an embedding into the
challenge field preserve these properties. This is the polynomial input to the
disjoint-padding and pole-reduction argument for the actual extension domain.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow
open Polynomial Gold
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxRecDepth 2048

/-- The Gold family used for Longfellow, on any prescribed affine binary
11-space and after any embedding into the challenge field. The hypotheses
specify only field sizes and the domain, not a supplied polynomial family. -/
theorem exists_seed_family
    {B F : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    [Field F] [Fintype F] (φ : B →+* F)
    (D : AddSubgroup B) [Fintype D] (a : B)
    (hB : Fintype.card B=2^16) (hD : Nat.card D=2^11) :
    let U := affineDomain (additiveDomain (D.map φ.toAddMonoidHom)) (φ a)
    ∃ R : F[X], ∃ ps : Finset F[X], ps.card=5843376 ∧
      ∀ p∈ps, (p-R).natDegree=384 ∧
        768≤(U.filter fun x => p.eval x=0).card := by
  classical
  obtain ⟨e⟩ := exists_gold_basis D 11 hD
  have hpop := card_momentTensors_lower_bound D 16 11 2 hB hD e
    (by decide) (by decide) (by decide)
  have hnum : (2^(16-2*(16-11+if Even 11 then 1 else 0))-1)*
      gaussianBinomial 4 (11/2) 2=365211 := by
    rw [ite_eq_right (by decide : ¬Even 11)]
    norm_num [gaussianBinomial, Finset.prod_range_succ]
  rw [hnum] at hpop
  obtain ⟨allLocators,hallCard,hall⟩ := exists_repairedLocator_family D 10 hD
    (basisParameter D e) e (basisParameter_eval D e) 2 (by decide) (by decide)
  have hsize : 5843376≤allLocators.card := by rw [hallCard]; norm_num; omega
  obtain ⟨ps,hsub,hcard⟩ := Finset.exists_subset_card_eq hsize
  let shift : F[X] := X-C (φ a)
  let tr : B[X] → F[X] := fun p => (p.map φ).comp shift
  have htr : Function.Injective tr := by
    intro p q hpq
    have he := congrArg (fun r : F[X] => r.comp (X+C (φ a))) hpq
    have hc : shift.comp (X+C (φ a))=X := by simp [shift]
    simp only [tr,comp_assoc,hc,comp_X] at he
    exact Polynomial.map_injective φ φ.injective he
  refine ⟨-tr (goldSourcePolynomial D 10),ps.image tr,?_,?_⟩
  · rw [Finset.card_image_iff.mpr htr.injOn,hcard]
  · intro p hp
    obtain ⟨p0,hp0,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨A,hA,l,κ,rfl,hzero⟩ := hall p0 (hsub hp0)
    obtain ⟨hr,hM⟩ := (mem_momentTensors D (basisParameter D e) 2 A).mp hA
    have hprop := repairedLocator_properties D 10 hD (basisParameter D e) A l κ 2
      (by decide) (by decide) hM hr hzero
    constructor
    · rw [sub_neg_eq_add]
      have he : tr (repairedLocator D (basisParameter D e) A l κ 2) +
          tr (goldSourcePolynomial D 10) =
          tr (repairedLocator D (basisParameter D e) A l κ 2+goldSourcePolynomial D 10) := by
        simp [tr,Polynomial.map_add,add_comp]
      rw [he]
      simp only [tr,shift,natDegree_comp,natDegree_X_sub_C,mul_one,natDegree_map]
      exact hprop.2.2.1
    · let p := repairedLocator D (basisParameter D e) A l κ 2
      have hc := agreementCount_affineDomain (additiveDomain (D.map φ.toAddMonoidHom))
        (φ a) (fun _ : F => 0) (tr p)
      have he : (tr p).comp (X+C (φ a))=p.map φ := by simp [tr,shift,comp_assoc]
      rw [he] at hc
      rw [agreementCount_eq_card_filter _ (fun _ : F => 0) (tr p),
        agreementCount_eq_card_filter _ (fun _ : F => 0) (p.map φ)] at hc
      change 768≤((affineDomain (additiveDomain (D.map φ.toAddMonoidHom)) (φ a)).filter
        fun x => (tr p).eval x=0).card
      rw [hc,card_mapped_locator_roots]
      exact hprop.2.2.2.1.ge
end BinaryFieldCounterexamples.Longfellow
