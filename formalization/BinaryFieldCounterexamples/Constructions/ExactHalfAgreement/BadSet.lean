/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.Hyperplanes
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.Converse

/-!
# The exact half-agreement exceptional set
-/

@[expose] public section

namespace BinaryFieldCounterexamples.ExactHalf

open Polynomial
open BinaryFieldCounterexamples.Gold

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- Monicity uniquely fixes the scalar used to normalize a nonconstant affine
functional polynomial. -/
theorem scaled_functional_eq_affineHyperplaneLocator_of_monic
    (D : AddSubgroup F) [Fintype D] (l : D →+ ZMod 2) (hl : l ≠ 0)
    (b : ZMod 2) (c : F)
    (hmonic : (C c * (functionalPolynomial D l +
      C (algebraMap (ZMod 2) F b))).Monic) :
    C c * (functionalPolynomial D l + C (algebraMap (ZMod 2) F b)) =
      affineHyperplaneLocator D l b := by
  let P := functionalPolynomial D l
  have hdeg := natDegree_functionalPolynomial_of_ne D l hl
  change P.natDegree = Nat.card D / 2 at hdeg
  have hpos : 0 < P.natDegree := by
    have hc := card_functionalKernel_mul_two D l hl
    have hkpos : 0 < Nat.card (functionalKernel D l) := Nat.card_pos
    omega
  have hlc : P.leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    intro hP
    rw [hP, natDegree_zero] at hpos
    omega
  have hconstdeg : (C (algebraMap (ZMod 2) F b)).natDegree < P.natDegree := by
    calc
      _ ≤ 0 := (natDegree_C _).le
      _ < _ := hpos
  have haddlc : (P + C (algebraMap (ZMod 2) F b)).leadingCoeff = P.leadingCoeff :=
    leadingCoeff_add_of_degree_lt' (degree_lt_degree hconstdeg)
  have hc : c = P.leadingCoeff⁻¹ := by
    have hm := hmonic.leadingCoeff
    change (C c * (P + C (algebraMap (ZMod 2) F b))).leadingCoeff = 1 at hm
    rw [leadingCoeff_mul, leadingCoeff_C, haddlc] at hm
    rw [inv_eq_one_div]
    exact (eq_div_iff hlc).mpr hm
  rw [hc]
  rfl

/-- The shifted exterior evaluations that occur as half-agreement challenges. -/
noncomputable def affineHyperplaneChallenges
    (D : AddSubgroup F) [Fintype D] (β : F) : Finset F := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  exact (affineHyperplaneIndices D).image fun p ↦
    (affineHyperplaneLocator D p.1 p.2).eval β +
      (binaryQuarterNumerator D β).eval β

/-- Translation by the fixed numerator value preserves the exact challenge count. -/
theorem card_affineHyperplaneChallenges
    (D : AddSubgroup F) [Fintype D] {β : F} (hβ : β ∉ D) :
    (affineHyperplaneChallenges D β).card = 2 * (Nat.card D - 1) := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  rw [affineHyperplaneChallenges, Finset.card_image_iff.mpr]
  · exact card_affineHyperplaneIndices D
  · intro p hp q hq heq
    apply affineHyperplaneLocator_eval_injOn D hβ hp hq
    exact add_right_cancel heq

/-- At exact half agreement, the complete exceptional set is precisely the
shifted affine-hyperplane evaluation family. -/
theorem badChallenges_eq_affineHyperplaneChallenges
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4 * K) :
    badChallenges (additiveDomain D) K
        (fun x ↦ (binaryQuarterNumerator D β).eval (x : F) * ((x : F) - β)⁻¹)
        (fun x ↦ ((x : F) - β)⁻¹) (2 * K) =
      affineHyperplaneChallenges D β := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨l, b, c, hl, hc, hmonic, hAS, hzrep⟩ :=
      halfAgreement_bad_representation D β hβ K hK hcard z hz
    have hnorm := scaled_functional_eq_affineHyperplaneLocator_of_monic
      D l hl b c hmonic
    rw [affineHyperplaneChallenges, Finset.mem_image]
    refine ⟨(l, b), ?_, ?_⟩
    · rw [affineHyperplaneIndices, Finset.mem_product]
      exact ⟨Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩, Finset.mem_univ b⟩
    · rw [← hnorm, hzrep, CharTwo.sub_eq_add]
  · intro z hz
    rw [affineHyperplaneChallenges, Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hl : p.1 ≠ 0 := by
      rw [affineHyperplaneIndices, Finset.mem_product] at hp
      exact (Finset.mem_erase.mp hp.1).1
    exact affineHyperplane_badChallenge D β hβ K hK hcard p.1 hl p.2

/-- The exact half-agreement exceptional set has `2 (|D|-1)` distinct challenges. -/
theorem card_binaryQuarter_badChallenges
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4 * K) :
    (badChallenges (additiveDomain D) K
        (fun x ↦ (binaryQuarterNumerator D β).eval (x : F) * ((x : F) - β)⁻¹)
        (fun x ↦ ((x : F) - β)⁻¹) (2 * K)).card =
      2 * (Nat.card D - 1) := by
  rw [badChallenges_eq_affineHyperplaneChallenges D β hβ K hK hcard,
    card_affineHyperplaneChallenges D hβ]

end BinaryFieldCounterexamples.ExactHalf
