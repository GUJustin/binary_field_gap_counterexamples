/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.Parameters
public import BinaryFieldCounterexamples.Polynomial.ArtinSchreier
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound
public import BinaryFieldCounterexamples.Constructions.PoleReduction
public import BinaryFieldCounterexamples.Agreement.Domains

@[expose] public section

namespace BinaryFieldCounterexamples.ExactHalf

open Polynomial
open BinaryFieldCounterexamples.Gold

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The points of the prescribed domain in one binary functional fiber. -/
def functionalFiber (D : AddSubgroup F) [Fintype D]
    (l : D →+ ZMod 2) (b : ZMod 2) : Finset D :=
  Finset.univ.filter fun x ↦ l x = b

/-- Every fiber of a nonzero binary functional contains half the domain. -/
theorem card_functionalFiber (D : AddSubgroup F) [Fintype D]
    (l : D →+ ZMod 2) (hl : l ≠ 0)
    (b : ZMod 2) : (functionalFiber D l b).card = Nat.card D / 2 := by
  classical
  obtain ⟨y, hy⟩ := binaryFunctional_surjective l hl b
  let e : l.ker ≃ functionalFiber D l b :=
    { toFun := fun x ↦ ⟨x + y, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          rw [map_add, x.property, hy, zero_add]⟩⟩
      invFun := fun x ↦ ⟨x - y, by
        have hx := (Finset.mem_filter.mp x.property).2
        change l ((x : D) - y) = 0
        rw [map_sub, hx, hy, sub_self]⟩
      left_inv := fun x ↦ by ext; simp
      right_inv := fun x ↦ by ext; simp }
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr e]
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup l.ker
  have he := QuotientAddGroup.quotientKerEquivOfSurjective l
    (binaryFunctional_surjective l hl)
  have hq : Nat.card (D ⧸ l.ker) = 2 := by
    rw [Nat.card_congr he.toEquiv, Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [hq] at hc
  omega

/-- The canonical monic locator of an affine binary hyperplane. -/
noncomputable def affineHyperplaneLocator
    (D : AddSubgroup F) [Fintype D] (l : D →+ ZMod 2) (b : ZMod 2) : F[X] :=
  let P := functionalPolynomial D l
  C P.leadingCoeff⁻¹ * (P + C (algebraMap (ZMod 2) F b))

/-- A nonzero functional polynomial has exact half-domain degree. -/
theorem natDegree_functionalPolynomial_of_ne
    (D : AddSubgroup F) [Fintype D] (l : D →+ ZMod 2) (hl : l ≠ 0) :
    (functionalPolynomial D l).natDegree = Nat.card D / 2 := by
  classical
  let P := functionalPolynomial D l
  have hupper := (functionalPolynomial_support_and_degree D l).2
  have hP : P ≠ 0 := by
    intro hz
    apply hl
    apply functionalPolynomial_injective D
    simpa only [P, functionalPolynomial_zero] using hz
  have hroots : (functionalFiber D l 0).card ≤ P.natDegree := by
    have hmap : Set.MapsTo Subtype.val (↑(functionalFiber D l 0) : Set D)
        (↑P.roots.toFinset : Set F) := by
      intro x hx
      apply Multiset.mem_toFinset.mpr
      rw [mem_roots hP]
      have hx0 := (Finset.mem_filter.mp hx).2
      simpa [P, functionalPolynomial_eval, hx0]
    exact (Finset.card_le_card_of_injOn Subtype.val hmap
      Subtype.val_injective.injOn).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' P))
  rw [card_functionalFiber D l hl 0] at hroots
  change P.natDegree ≤ Nat.card D / 2 at hupper
  exact le_antisymm hupper hroots

/-- The affine locator is monic of exact half-domain degree. -/
theorem affineHyperplaneLocator_monic_natDegree
    (D : AddSubgroup F) [Fintype D]
    (l : D →+ ZMod 2) (hl : l ≠ 0) (b : ZMod 2) :
    (affineHyperplaneLocator D l b).Monic ∧
      (affineHyperplaneLocator D l b).natDegree = Nat.card D / 2 := by
  classical
  let P := functionalPolynomial D l
  have hdeg := natDegree_functionalPolynomial_of_ne D l hl
  change P.natDegree = Nat.card D / 2 at hdeg
  have hpos : 0 < Nat.card D / 2 := by
    have hc := card_functionalKernel_mul_two D l hl
    have hkpos : 0 < Nat.card (functionalKernel D l) := Nat.card_pos
    omega
  have hlc : P.leadingCoeff ≠ 0 := by
    exact leadingCoeff_ne_zero.mpr (by
      intro hz
      rw [hz, natDegree_zero] at hdeg
      omega)
  have hconstdeg : (C (algebraMap (ZMod 2) F b)).natDegree < P.natDegree := by
    calc
      _ ≤ 0 := (natDegree_C _).le
      _ < _ := by omega
  have hadddeg : (P + C (algebraMap (ZMod 2) F b)).natDegree = P.natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hconstdeg
  have haddlc : (P + C (algebraMap (ZMod 2) F b)).leadingCoeff = P.leadingCoeff :=
    leadingCoeff_add_of_degree_lt' (degree_lt_degree hconstdeg)
  constructor
  · have hsum : P + C (algebraMap (ZMod 2) F b) ≠ 0 := by
      exact leadingCoeff_ne_zero.mp (haddlc.trans_ne hlc)
    have hm := monic_mul_leadingCoeff_inv hsum
    rw [haddlc] at hm
    simpa only [affineHyperplaneLocator, mul_comm] using hm
  · simp only [affineHyperplaneLocator]
    rw [natDegree_C_mul (inv_ne_zero hlc), hadddeg, hdeg]

/-- On the prescribed domain, the affine locator vanishes exactly on its
functional fiber. -/
theorem affineHyperplaneLocator_eval_eq_zero_iff
    (D : AddSubgroup F) [Fintype D] (l : D →+ ZMod 2) (hl : l ≠ 0)
    (b : ZMod 2) (x : D) :
    (affineHyperplaneLocator D l b).eval (x : F) = 0 ↔ l x = b := by
  classical
  let P := functionalPolynomial D l
  have hlc : P.leadingCoeff ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    intro hzero
    apply hl
    apply functionalPolynomial_injective D
    simpa only [P, functionalPolynomial_zero] using hzero
  rw [affineHyperplaneLocator, eval_mul, eval_C, eval_add,
    functionalPolynomial_eval]
  simp only [eval_C]
  have hlc' : (functionalPolynomial D l).leadingCoeff ≠ 0 := by
    simpa only [P] using hlc
  rw [mul_eq_zero]
  simp only [inv_eq_zero, hlc', false_or, ← map_add, map_eq_zero]
  exact CharTwo.add_eq_zero (R := ZMod 2)


end BinaryFieldCounterexamples.ExactHalf

namespace BinaryFieldCounterexamples.ExactHalf

open Polynomial
open BinaryFieldCounterexamples.Gold

/-- The leading coefficient normalizes the functional Artin--Schreier scalar. -/
theorem functionalPolynomial_leadingCoeff_sq
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (l : D →+ ZMod 2) (hl : l ≠ 0) :
    (functionalPolynomial D l).leadingCoeff ^ 2 =
      (functionalPolynomial D l).coeff 1 * ((subspacePolynomial D).coeff 1)⁻¹ := by
  let P := functionalPolynomial D l
  let L := subspacePolynomial D
  have hdeg := natDegree_functionalPolynomial_of_ne D l hl
  change P.natDegree = Nat.card D / 2 at hdeg
  have hpos : 0 < P.natDegree := by
    have hc := card_functionalKernel_mul_two D l hl
    have hkpos : 0 < Nat.card (Gold.functionalKernel D l) := Nat.card_pos
    omega
  have hP : P ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hpos
    omega
  have hp1 : P.coeff 1 ≠ 0 := by
    intro hz
    apply hl
    apply functionalLinearCoefficient_injective D
    change P.coeff 1 = (functionalPolynomial D 0).coeff 1
    simpa only [functionalPolynomial_zero, coeff_zero]
  have hscalar : P.coeff 1 * (L.coeff 1)⁻¹ ≠ 0 :=
    mul_ne_zero hp1 (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero D))
  have hlt : P.degree < (P ^ 2).degree := by
    apply degree_lt_degree
    rw [natDegree_pow, hdeg]
    omega
  have h := congrArg leadingCoeff (functionalPolynomial_artinSchreier D l)
  change (P ^ 2 + P).leadingCoeff =
    (C (P.coeff 1) * (C ((L.coeff 1)⁻¹) * L)).leadingCoeff at h
  rw [leadingCoeff_add_of_degree_lt' hlt, leadingCoeff_pow,
    leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_C,
    (subspacePolynomial_monic D).leadingCoeff, mul_one] at h
  simpa only [mul_assoc] using h

/-- A normalized affine hyperplane locator has an Artin--Schreier image equal
to the full domain locator. -/
theorem affineHyperplaneLocator_artinSchreier
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (l : D →+ ZMod 2) (hl : l ≠ 0)
    (b : ZMod 2) :
    (affineHyperplaneLocator D l b) ^ 2 +
        C ((functionalPolynomial D l).leadingCoeff⁻¹) *
          affineHyperplaneLocator D l b = subspacePolynomial D := by
  let P := functionalPolynomial D l
  let L := subspacePolynomial D
  let e : F := algebraMap (ZMod 2) F b
  let r := P.leadingCoeff
  have hr : r ≠ 0 := by
    apply leadingCoeff_ne_zero.mpr
    intro hz
    apply hl
    apply functionalPolynomial_injective D
    simpa only [P, functionalPolynomial_zero] using hz
  have hrsq := functionalPolynomial_leadingCoeff_sq D l hl
  change r ^ 2 = P.coeff 1 * (L.coeff 1)⁻¹ at hrsq
  have hL1 : L.coeff 1 ≠ 0 := subspacePolynomial_coeff_one_ne_zero D
  have hAS := functionalPolynomial_artinSchreier D l
  change P ^ 2 + P = C (P.coeff 1) * (C ((L.coeff 1)⁻¹) * L) at hAS
  have he : e ^ 2 = e := by
    rcases binary_eq_zero_or_one b with hb | hb
    · simp [e, hb]
    · simp [e, hb]
  change (C r⁻¹ * (P + C e)) ^ 2 + C r⁻¹ * (C r⁻¹ * (P + C e)) = L
  rw [mul_pow, CharTwo.add_sq]
  simp only [← C_pow, he]
  have hcollapse :
      C (r⁻¹ ^ 2) * (P ^ 2 + C e) + C r⁻¹ * (C r⁻¹ * (P + C e)) =
        C (r⁻¹ ^ 2) * (P ^ 2 + P) := by
    rw [← mul_assoc (C r⁻¹) (C r⁻¹), ← C_mul, ← pow_two]
    change C (r⁻¹ ^ 2) * (P ^ 2 + C e) +
      C (r⁻¹ ^ 2) * (P + C e) = C (r⁻¹ ^ 2) * (P ^ 2 + P)
    have hce : C (r⁻¹ ^ 2) * C e + C e * C (r⁻¹ ^ 2) = 0 := by
      rw [mul_comm]
      exact CharTwo.add_self_eq_zero _
    ring_nf
    linear_combination hce
  rw [hcollapse, hAS]
  rw [← mul_assoc (C (r⁻¹ ^ 2)) (C (P.coeff 1)), ← C_mul,
    ← mul_assoc (C (r⁻¹ ^ 2 * P.coeff 1)) (C (L.coeff 1)⁻¹), ← C_mul]
  rw [show r⁻¹ ^ 2 * P.coeff 1 * (L.coeff 1)⁻¹ = 1 by
    rw [mul_assoc, ← hrsq]
    field_simp]
  rw [C_1, one_mul]

end BinaryFieldCounterexamples.ExactHalf

namespace BinaryFieldCounterexamples.ExactHalf

open Polynomial
open BinaryFieldCounterexamples.Gold

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The affine functional and bit are recovered from their monic locator. -/
theorem affineHyperplaneLocator_injective
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D]
    {l k : D →+ ZMod 2} (hl : l ≠ 0) (hk : k ≠ 0)
    {b d : ZMod 2}
    (h : affineHyperplaneLocator D l b = affineHyperplaneLocator D k d) :
    l = k ∧ b = d := by
  have hfiber : ∀ x : D, (l x = b ↔ k x = d) := by
    intro x
    rw [← affineHyperplaneLocator_eval_eq_zero_iff D l hl b x,
      ← affineHyperplaneLocator_eval_eq_zero_iff D k hk d x, h]
  have hbd : b = d := by
    have hzero := hfiber (0 : D)
    simp only [map_zero] at hzero
    rcases binary_eq_zero_or_one b with hb | hb <;>
      rcases binary_eq_zero_or_one d with hd | hd <;> simp_all
  subst d
  constructor
  · ext x
    have hx := hfiber x
    rcases binary_eq_zero_or_one b with hb | hb <;>
      rcases binary_eq_zero_or_one (l x) with hlx | hlx <;>
      rcases binary_eq_zero_or_one (k x) with hkx | hkx <;> simp_all
  · rfl

/-- The finite family indexing all nonconstant affine binary hyperplanes. -/
noncomputable def affineHyperplaneIndices (D : AddSubgroup F) [Fintype D] :
    Finset ((D →+ ZMod 2) × ZMod 2) := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  exact ((Finset.univ.erase 0 : Finset (D →+ ZMod 2)) ×ˢ
    (Finset.univ : Finset (ZMod 2)))

/-- The affine-hyperplane index family has exactly `2 (|D|-1)` members. -/
theorem card_affineHyperplaneIndices (D : AddSubgroup F) [Fintype D] :
    (affineHyperplaneIndices D).card = 2 * (Nat.card D - 1) := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  rw [affineHyperplaneIndices, Finset.card_product, Finset.card_erase_of_mem
    (Finset.mem_univ (0 : D →+ ZMod 2))]
  simp only [Finset.card_univ, ZMod.card, Nat.card_eq_fintype_card]
  have hdual : Fintype.card (D →+ ZMod 2) = Fintype.card D := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2
        (M := D) (M₁ := ZMod 2)).toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)]
  rw [hdual]
  omega

/-- Exterior evaluation is injective on the affine-hyperplane locator family. -/
theorem affineHyperplaneLocator_eval_injOn
    (D : AddSubgroup F) [Fintype D] {β : F} (hβ : β ∉ D) :
    Set.InjOn (fun p : (D →+ ZMod 2) × ZMod 2 ↦
      (affineHyperplaneLocator D p.1 p.2).eval β)
      (affineHyperplaneIndices D) := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  intro p hp q hq heval
  change p ∈ ((Finset.univ.erase 0 : Finset (D →+ ZMod 2)) ×ˢ
    (Finset.univ : Finset (ZMod 2))) at hp
  change q ∈ ((Finset.univ.erase 0 : Finset (D →+ ZMod 2)) ×ˢ
    (Finset.univ : Finset (ZMod 2))) at hq
  have hp0 : p.1 ≠ 0 := by
    exact (Finset.mem_product.mp hp).1 |> Finset.mem_erase.mp |>.1
  have hq0 : q.1 ≠ 0 := by
    exact (Finset.mem_product.mp hq).1 |> Finset.mem_erase.mp |>.1
  have hLβ : (subspacePolynomial D).eval β ≠ 0 := by
    intro hz
    apply hβ
    exact (subspacePolynomial_eval_eq_zero_iff D β).mp hz
  have hpoly := artinSchreier_eval_injective
    (affineHyperplaneLocator D p.1 p.2)
    (affineHyperplaneLocator D q.1 q.2) (subspacePolynomial D)
    (functionalPolynomial D p.1).leadingCoeff⁻¹
    (functionalPolynomial D q.1).leadingCoeff⁻¹ β
    (affineHyperplaneLocator_artinSchreier D p.1 hp0 p.2)
    (affineHyperplaneLocator_artinSchreier D q.1 hq0 q.2) hLβ heval
  rcases affineHyperplaneLocator_injective D hp0 hq0 hpoly with ⟨hl, hb⟩
  exact Prod.ext hl hb

/-- The exterior evaluations of all nonconstant affine-hyperplane locators. -/
noncomputable def affineHyperplaneLabels
    (D : AddSubgroup F) [Fintype D] (β : F) : Finset F := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  exact (affineHyperplaneIndices D).image fun p ↦
    (affineHyperplaneLocator D p.1 p.2).eval β

/-- The set of exterior affine-hyperplane challenges has the paper's exact size. -/
theorem card_affineHyperplaneLabels
    (D : AddSubgroup F) [Fintype D] {β : F} (hβ : β ∉ D) :
    (affineHyperplaneLabels D β).card = 2 * (Nat.card D - 1) := by
  classical
  letI : Fintype (D →+ ZMod 2) :=
    Fintype.ofInjective (fun l : D →+ ZMod 2 ↦ (l : D → ZMod 2)) DFunLike.coe_injective
  rw [affineHyperplaneLabels,
    Finset.card_image_iff.mpr (affineHyperplaneLocator_eval_injOn D hβ),
    card_affineHyperplaneIndices]

end BinaryFieldCounterexamples.ExactHalf

namespace BinaryFieldCounterexamples.ExactHalf

open Polynomial
open BinaryFieldCounterexamples.Gold

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The correction from the canonical quarter-rate numerator to an affine
hyperplane locator has degree at most the message degree. -/
theorem binaryQuarter_affineHyperplane_difference_natDegree_le
    (D : AddSubgroup F) [Fintype D] (β : F) (K : ℕ) (hK : 2 ≤ K)
    (hcard : Fintype.card D = 4 * K)
    (l : D →+ ZMod 2) (hl : l ≠ 0) (b : ZMod 2) :
    (binaryQuarterNumerator D β + affineHyperplaneLocator D l b).natDegree ≤ K := by
  let S := binaryQuarterNumerator D β
  let A := affineHyperplaneLocator D l b
  let L := subspacePolynomial D
  let lam := L.coeff 1
  let c := (functionalPolynomial D l).leadingCoeff⁻¹
  have hSsq := binaryQuarterNumerator_sq D β
  change S ^ 2 = L - C lam * (X - C β) at hSsq
  have hAS := affineHyperplaneLocator_artinSchreier D l hl b
  change A ^ 2 + C c * A = L at hAS
  have hAdeg : A.natDegree = 2 * K := by
    have h := (affineHyperplaneLocator_monic_natDegree D l hl b).2
    change A.natDegree = Nat.card D / 2 at h
    rw [Nat.card_eq_fintype_card, hcard] at h
    omega
  have hA2 : A ^ 2 = L + C c * A := by
    rw [← CharTwo.sub_eq_add, eq_sub_iff_add_eq]
    exact hAS
  have hsq : (S + A) ^ 2 = C lam * (X - C β) + C c * A := by
    rw [CharTwo.add_sq, hSsq, hA2, CharTwo.sub_eq_add]
    calc
      (L + C lam * (X - C β)) + (L + C c * A) =
          (L + L) + (C lam * (X - C β) + C c * A) := by ac_rfl
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
  have hrhs : (C lam * (X - C β) + C c * A).natDegree ≤ 2 * K := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      rw [natDegree_C, natDegree_X_sub_C]
      omega
    · apply natDegree_mul_le.trans
      rw [natDegree_C, hAdeg]
      omega
  have hleft : 2 * (S + A).natDegree ≤ 2 * K := by
    rw [← natDegree_pow, hsq]
    exact hrhs
  change (S + A).natDegree ≤ K
  omega

/-- Every affine hyperplane produces a half-agreement challenge for the fixed
quarter-rate reciprocal received pair. -/
theorem affineHyperplane_badChallenge
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4 * K)
    (l : D →+ ZMod 2) (hl : l ≠ 0) (b : ZMod 2) :
    (affineHyperplaneLocator D l b).eval β +
        (binaryQuarterNumerator D β).eval β ∈
      badChallenges (additiveDomain D) K
        (fun x : additiveDomain D ↦
          (binaryQuarterNumerator D β).eval (x : F) * ((x : F) - β)⁻¹)
        (fun x : additiveDomain D ↦ ((x : F) - β)⁻¹) (2 * K) := by
  classical
  let S := binaryQuarterNumerator D β
  let A := affineHyperplaneLocator D l b
  let C := S + A
  have hCnat : C.natDegree ≤ K := by
    simpa only [C, S, A] using
      binaryQuarter_affineHyperplane_difference_natDegree_le D β K hK hcard l hl b
  have hCdeg : C.degree ≤ (K : WithBot ℕ) := degree_le_of_natDegree_le hCnat
  have hroots : 2 * K ≤
      ((additiveDomain D).filter fun x ↦ (S + C).eval x = 0).card := by
    let fiber := functionalFiber D l b
    have hmap : Set.MapsTo (fun x : D ↦ (x : F)) (↑fiber : Set D)
        (↑((additiveDomain D).filter fun x ↦ (S + C).eval x = 0) : Set F) := by
      intro x hx
      apply Finset.mem_filter.mpr
      have hxD : (x : F) ∈ additiveDomain D :=
        (BinaryFieldCounterexamples.mem_additiveDomain D (x : F)).mpr x.property
      refine ⟨hxD, ?_⟩
      have hAx : A.eval (x : F) = 0 :=
        (affineHyperplaneLocator_eval_eq_zero_iff D l hl b x).mpr
          (Finset.mem_filter.mp hx).2
      simp only [C, eval_add]
      rw [show S.eval (x : F) + (S.eval (x : F) + A.eval (x : F)) = 0 by
        rw [hAx, add_zero, CharTwo.add_self_eq_zero]]
    have hle := Finset.card_le_card_of_injOn (fun x : D ↦ (x : F)) hmap
      Subtype.val_injective.injOn
    rw [card_functionalFiber D l hl b, Nat.card_eq_fintype_card, hcard] at hle
    omega
  have hβD : β ∉ additiveDomain D := by
    intro hb
    exact hβ ((BinaryFieldCounterexamples.mem_additiveDomain D β).mp hb)
  have hbad := poleReduction_badChallenge (additiveDomain D) β hβD
    S C K (2 * K) hCdeg hroots
  simpa only [C, eval_add, add_comm] using hbad

end BinaryFieldCounterexamples.ExactHalf
