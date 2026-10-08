/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Domains
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.SourceBound
public import BinaryFieldCounterexamples.Constructions.ExactHalfAgreement.FunctionalCharacterization

/-!
# The converse to exact half agreement

Saturating a monic residual's root bound makes it divide the domain locator.
The square-minus-locator residual has small enough degree that the quotient is
a constant. Its nonzero derivative forces that constant to be nonzero, yielding
the quadratic identity that characterizes affine binary hyperplane locators.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Polynomial
/-- A monic polynomial whose degree is exhausted by distinct common roots
must divide every polynomial vanishing on those roots. -/
theorem monic_dvd_of_card_le_common_roots
    {F : Type*} [Field F] (S : Finset F) (A L : F[X]) (hA : A.Monic)
    (hcard : A.natDegree ≤ S.card)
    (hrootA : ∀ x ∈ S, A.eval x = 0)
    (hrootL : ∀ x ∈ S, L.eval x = 0) : A ∣ L := by
  classical
  have hdvd (P : F[X]) (hP : ∀ x ∈ S, P.eval x = 0) :
      (∏ x ∈ S, (X - C x : F[X])) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro x hx y hy hxy
      exact pairwise_coprime_X_sub_C Function.injective_id hxy
    · intro x hx
      exact dvd_iff_isRoot.mpr (hP x hx)
  have heq : A = ∏ x ∈ S, (X-C x : F[X]) := by
    refine eq_of_monic_of_dvd_of_natDegree_le
      (monic_prod_of_monic S (fun x : F => X-C x) (fun x hx => monic_X_sub_C x))
      hA (hdvd A hrootA) ?_
    simpa only [natDegree_finsetProd_X_sub_C_eq_card] using hcard
  rw [heq]
  exact hdvd L hrootL
/-- The canonical square-root numerator has the exact monic leading term. -/
theorem binaryQuarterNumerator_monic_natDegree
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β : F)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4*K) :
    (binaryQuarterNumerator D β).Monic ∧
      (binaryQuarterNumerator D β).natDegree = 2*K := by
  let L := subspacePolynomial D
  have hdeg : L.natDegree = 4*K := by
    simp only [L, subspacePolynomial_natDegree, hcard]
  have hsmall : (C (L.coeff 1)*(X-C β)).natDegree < L.natDegree := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, natDegree_X_sub_C, hdeg]
    omega
  have hsq : (binaryQuarterNumerator D β)^2 = L-C (L.coeff 1)*(X-C β) :=
    binaryQuarterNumerator_sq D β
  have hm : ((binaryQuarterNumerator D β)^2).Monic := by
    rw [hsq]
    exact (subspacePolynomial_monic D).sub_of_left (degree_lt_degree hsmall)
  constructor
  · apply CharTwo.sq_injective
    simpa only [leadingCoeff_pow, one_pow] using hm.leadingCoeff
  · have hd := congrArg natDegree hsq
    rw [natDegree_pow, natDegree_sub_eq_left_of_natDegree_lt hsmall, hdeg] at hd
    omega
/-- A half-agreement residual is an affine hyperplane polynomial: saturation
of its roots forces its quadratic locator identity. -/
theorem halfAgreementResidual_artinSchreier
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) [Fintype D] (β z : F)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4*K)
    (h : F[X]) (hh : h.degree < (K : WithBot ℕ))
    (R : Finset F) (hRD : ∀ x ∈ R, x ∈ D) (hR : 2*K ≤ R.card)
    (hroot : ∀ x ∈ R,
      (binaryQuarterNumerator D β + C z - (X-C β)*h).eval x = 0) :
    let A := binaryQuarterNumerator D β + C z - (X-C β)*h
    A.Monic ∧ A.natDegree = 2*K ∧
      ∃ c : F, c ≠ 0 ∧ A^2+C c*A = subspacePolynomial D := by
  classical
  let S := binaryQuarterNumerator D β
  let L := subspacePolynomial D
  let T := C z - (X-C β)*h
  let A := S+T
  let Q := A^2-L
  have hhnat : h.natDegree ≤ K-1 := by
    by_cases hz : h=0
    · simp [hz]
    have := (natDegree_lt_iff_degree_lt hz).mpr hh
    omega
  have hTdeg : T.natDegree ≤ K := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · apply natDegree_mul_le.trans
      rw [natDegree_X_sub_C]
      omega
  obtain ⟨hSm, hSdeg⟩ := binaryQuarterNumerator_monic_natDegree D β K hK hcard
  have hTS : T.natDegree < S.natDegree := by change T.natDegree < (binaryQuarterNumerator D β).natDegree; rw [hSdeg]; omega
  have hAm : A.Monic := hSm.add_of_left (degree_lt_degree hTS)
  have hAdeg : A.natDegree = 2*K := by
    exact (natDegree_add_eq_left_of_natDegree_lt hTS).trans hSdeg
  have hQform : Q = T^2-C (L.coeff 1)*(X-C β) := by
    dsimp [Q, A, S]
    rw [CharTwo.add_sq, binaryQuarterNumerator_sq, binaryQuarterRadicand]
    dsimp [L]
    ring
  have hQdeg : Q.natDegree ≤ 2*K := by
    rw [hQform]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hTdeg)
    · apply natDegree_mul_le.trans
      rw [natDegree_C, natDegree_X_sub_C]
      omega
  have hAL : A ∣ L := by
    apply monic_dvd_of_card_le_common_roots R A L hAm
    · omega
    · intro x hx
      simpa only [A, S, T, add_sub_assoc] using hroot x hx
    · intro x hx
      exact (subspacePolynomial_eval_eq_zero_iff D x).mpr (hRD x hx)
  have hAQ : A ∣ Q := dvd_sub (dvd_pow_self A (by decide)) hAL
  have hQeq : Q = C Q.leadingCoeff*A :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hAm hAQ (by omega)
  have hAS : A^2+C Q.leadingCoeff*A = L := by
    rw [← hQeq]
    dsimp [Q]
    rw [CharTwo.sub_eq_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hc : Q.leadingCoeff ≠ 0 := by
    intro hc
    have hd := congrArg derivative hAS
    have hLder : L.derivative = C (L.coeff 1) :=
      Gold.derivative_eq_C_of_binarySupport L (subspacePolynomial_support D)
    simp only [hc, C_0, zero_mul, add_zero, derivative_pow, hLder] at hd
    simp only [Nat.cast_ofNat, CharTwo.two_eq_zero, C_0, zero_mul] at hd
    exact subspacePolynomial_coeff_one_ne_zero D ((C_eq_zero.mp hd.symm))
  change (S+C z-(X-C β)*h).Monic ∧
    (S+C z-(X-C β)*h).natDegree=2*K ∧ _
  have hAform : S+C z-(X-C β)*h=A := by dsimp [A,T]; ring
  rw [hAform]
  exact ⟨hAm,hAdeg,Q.leadingCoeff,hc,hAS⟩
/-- Every half-agreement challenge comes from a scaled, nonzero binary
functional and one of its two fibers. -/
theorem halfAgreement_bad_representation
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (D : AddSubgroup F) [Fintype D] (β : F) (hβ : β ∉ D)
    (K : ℕ) (hK : 2 ≤ K) (hcard : Fintype.card D = 4*K) (z : F)
    (hz : z ∈ badChallenges (additiveDomain D) K
      (fun x => (binaryQuarterNumerator D β).eval (x : F) * ((x : F)-β)⁻¹)
      (fun x => ((x : F)-β)⁻¹) (2*K)) :
    ∃ (l : D →+ ZMod 2) (b : ZMod 2) (c : F),
      l ≠ 0 ∧ c ≠ 0 ∧
      (C c*(Gold.functionalPolynomial D l+C (algebraMap (ZMod 2) F b))).Monic ∧
      (C c*(Gold.functionalPolynomial D l+C (algebraMap (ZMod 2) F b)))^2 +
        C c*(C c*(Gold.functionalPolynomial D l+C (algebraMap (ZMod 2) F b))) =
          subspacePolynomial D ∧
      z = (C c*(Gold.functionalPolynomial D l+C (algebraMap (ZMod 2) F b))).eval β -
        (binaryQuarterNumerator D β).eval β := by
  classical
  obtain ⟨h, hh, hcount⟩ := (mem_badChallenges _ _ _ _ _ z).mp hz
  let S := binaryQuarterNumerator D β
  let A := S+C z-(X-C β)*h
  let R := (additiveDomain D).filter (fun x => h.eval x = S.eval x*(x-β)⁻¹+z*(x-β)⁻¹)
  have hR : 2*K ≤ R.card := by
    rw [agreementCount_eq_card_filter (additiveDomain D)
      (fun x => S.eval x*(x-β)⁻¹+z*(x-β)⁻¹) h] at hcount
    exact hcount
  have hRD : ∀ x ∈ R, x ∈ D := by
    intro x hx
    exact (mem_additiveDomain D x).mp (Finset.mem_filter.mp hx).1
  have hroot : ∀ x ∈ R, A.eval x = 0 := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hden : x-β ≠ 0 := sub_ne_zero.mpr (fun he => hβ (he ▸ hRD x hx))
    simp only [A, eval_add, eval_sub, eval_C, eval_mul, eval_X]
    field_simp at he
    linear_combination -he
  obtain ⟨hAm,hAdeg,c,hc,hAS⟩ :=
    halfAgreementResidual_artinSchreier D β z K hK hcard h hh R hRD hR hroot
  change A.Monic at hAm
  change A.natDegree=2*K at hAdeg
  change A^2+C c*A=subspacePolynomial D at hAS
  have hdeg : A.degree < (Nat.card D : WithBot ℕ) := by
    rw [degree_eq_natDegree hAm.ne_zero, hAdeg, Nat.card_eq_fintype_card, hcard]
    exact_mod_cast (show 2*K<4*K by omega)
  obtain ⟨l,b,hrep⟩ := exists_functional_of_affine_artinSchreier D A c hc hdeg hAS
  have hl : l ≠ 0 := by
    intro hl
    have hd := hAdeg
    rw [hrep, hl, Gold.functionalPolynomial_zero, zero_add, ← C_mul, natDegree_C] at hd
    omega
  refine ⟨l,b,c,hl,hc,?_,?_,?_⟩
  · rw [← hrep]
    exact hAm
  · rw [← hrep]
    exact hAS
  · rw [← hrep]
    simp [A, S]
end BinaryFieldCounterexamples
