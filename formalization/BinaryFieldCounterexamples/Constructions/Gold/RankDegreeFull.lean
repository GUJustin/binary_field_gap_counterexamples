/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.PaddingRadicals
public import BinaryFieldCounterexamples.Constructions.Gold.MinimumRank
/-!
# Full rank and locator factorization statements

This module supplies the locator identity in Lemma 5.9 and the general-rank
lower degree bound in Remark 5.11, using the manuscript's actual radical.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- The polar radical in Lemma 5.9, embedded as a subgroup of the ambient field. -/
noncomputable def tensorRadicalDomain (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) : AddSubgroup B :=
  (LinearMap.ker (tensorPolarMap D v A)).toAddSubgroup.map D.subtype
/-- The finite radical subgroup used in Lemma 5.9 has its ambient-field finite instance. -/
noncomputable def tensorRadicalDomainFintype (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Fintype (tensorRadicalDomain D v A) := Fintype.ofFinite _
attribute [local instance] tensorRadicalDomainFintype
/-- Membership in the Lemma 5.9 radical is equivalent to membership in `D` and vanishing of `J`. -/
theorem mem_tensorRadicalDomain (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) (x : B) :
    x ∈ tensorRadicalDomain D v A ↔ ∃ y : D, (y : B) = x ∧ (tensorLinearPart D v A).eval (y : B) = 0 := by
  simp only [tensorRadicalDomain, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl, (tensorPolarFunctional_eq_zero_iff D v A y).mp hy⟩
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y, (tensorPolarFunctional_eq_zero_iff D v A y).mpr hy, rfl⟩
/-- Lemma 5.9: the actual radical has `N/2^(2t)` elements at rank `2t`. -/
theorem card_tensorRadicalDomain (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Nat.card (tensorRadicalDomain D v A) = Nat.card D / 2^(tensorPolarRank D v A) := by
  let e : tensorRadicalDomain D v A ≃ {y : D // (tensorLinearPart D v A).eval (y : B) = 0} :=
    { toFun := fun x ↦ ⟨⟨x.val, by
        obtain ⟨y, he, _⟩ := (mem_tensorRadicalDomain D v A x.val).mp x.property
        exact he ▸ y.property⟩, by
        obtain ⟨y, he, hy⟩ := (mem_tensorRadicalDomain D v A x.val).mp x.property
        simpa [he] using hy⟩
      invFun := fun y ↦ ⟨(y.val : B), (mem_tensorRadicalDomain D v A _).mpr ⟨y.val, rfl, y.property⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e, card_tensorLinearPart_zeros]
/-- Lemma 5.9, assembled saturated clause: `J = J_(d-t) L_V^(2^t)`, the
 endpoint coefficient is nonzero, the degree is `N/2^t`, and the radical has size `N/2^(2t)`. -/
theorem tensorLinearPart_radical_factorization
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht0 : 0 < t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t) :
    tensorLinearPart D v A = C ((tensorLinearPart D v A).coeff (2^(k+1-t))) *
        subspacePolynomial (tensorRadicalDomain D v A) ^ (2^t) ∧
      (tensorLinearPart D v A).coeff (2^(k+1-t)) ≠ 0 ∧
      (tensorLinearPart D v A).natDegree = 2^(k+1-t) ∧
      Nat.card (tensorRadicalDomain D v A) = 2^(k+1-2*t) := by
  classical
  let V := tensorRadicalDomain D v A
  let Q := frobeniusRoot t (tensorLinearPart D v A)
  have hs : ∀ n ∈ (tensorLinearPart D v A).support, 2^t ∣ n := by
    intro n hn
    obtain ⟨i, rfl, hi, _⟩ := tensorLinearPart_support_interval D k hD v A t hM n hn
    exact pow_dvd_pow 2 hi
  have hV : Nat.card V = 2^(k+1-2*t) := by
    rw [card_tensorRadicalDomain, hD, hr, Nat.pow_div ht (by decide : 0 < 2)]
  have hd := (tensorLinearPart_frobeniusRoot_saturation D k hD v A t ht0 ht hM hr).1
  have hdiv : subspacePolynomial V ∣ Q := by
    apply subspacePolynomial_dvd_of_eval_zero
    intro x
    apply (frobeniusRoot_eval_eq_zero_iff t _ hs x.val).mpr
    obtain ⟨y, he, hy⟩ := (mem_tensorRadicalDomain D v A x.val).mp x.property
    simpa [he] using hy
  have he : Q = subspacePolynomial V * C Q.leadingCoeff :=
    eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le (subspacePolynomial_monic V) hdiv (by
      rw [subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card, hV]
      exact hd.le)
  have hp := frobeniusRoot_pow t (tensorLinearPart D v A) hs
  have hfactor : tensorLinearPart D v A =
      C (Q.leadingCoeff ^ (2^t)) * subspacePolynomial V ^ (2^t) := by
    calc
      tensorLinearPart D v A = Q ^ (2^t) := hp.symm
      _ = C (Q.leadingCoeff ^ (2^t)) * subspacePolynomial V ^ (2^t) := by
        conv_lhs => rw [he]
        rw [mul_pow, ← C_pow, mul_comm]
  obtain ⟨_, hdegree, hcoeff⟩ := tensorLinearPart_endpoint_coefficients D k hD v A t ht0 ht hM hr
  have hlc : (tensorLinearPart D v A).coeff (2^(k+1-t)) = Q.leadingCoeff^(2^t) := by
    rw [← hdegree, coeff_natDegree, hfactor, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow,
      (subspacePolynomial_monic V).leadingCoeff, one_pow, mul_one]
  exact ⟨by simpa [hlc, V] using hfactor, hcoeff, hdegree, hV⟩
/-- Remark 5.11: every majority repair at arbitrary positive rank obeys the
 Artin--Schreier degree balance and both lower degree bounds, without moment hypotheses. -/
theorem repairedPolynomial_general_rank_degree
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (l : D →+ ZMod 2) (κ : ZMod 2) (r : ℕ) (hr0 : 0 < r) (hrle : 2*r ≤ k+1)
    (hr : tensorPolarRank D v A = 2*r)
    (hzeros : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} = 2^k+2^(k-r)) :
    repairedPolynomial D v A l κ ^ 2 + repairedPolynomial D v A l κ =
        normalizedLocator D * (repairedPolynomial D v A l κ).derivative ∧
      tensorLinearPart D v A ≠ 0 ∧
      2*(repairedPolynomial D v A l κ).natDegree = 2^(k+1)+(tensorLinearPart D v A).natDegree ∧
      2^k+2^(k-r) ≤ (repairedPolynomial D v A l κ).natDegree ∧
      2^(k+1-r) ≤ (tensorLinearPart D v A).natDegree := by
  classical
  let H := repairedPolynomial D v A l κ
  let J := tensorLinearPart D v A
  have hJ : J ≠ 0 := tensorLinearPart_ne_zero_of_rank_pos D v A (by omega)
  have hJ0 : J.coeff 0 = 0 := by
    by_contra h
    obtain ⟨i, hi⟩ := tensorLinearPart_support D v A 0 (mem_support_iff.mpr h)
    have : 0 < (2:ℕ)^i := by positivity
    omega
  have hJpos : 0 < J.natDegree := by
    by_contra h
    have he := eq_C_of_natDegree_eq_zero (show J.natDegree = 0 by omega)
    rw [hJ0, C_0] at he
    exact hJ he
  have hd : H.derivative.natDegree = J.natDegree := by
    rw [repairedPolynomial_derivative, natDegree_add_C]
  have hdne : H.derivative ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hd
    omega
  have hH : H ≠ 0 := by intro he; exact hdne (by rw [he, derivative_zero])
  have hΛ : normalizedLocator D ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero D)))
      (subspacePolynomial_monic D).ne_zero
  have hΛdeg : (normalizedLocator D).natDegree = 2^(k+1) := by
    rw [normalizedLocator, natDegree_C_mul (inv_ne_zero (subspacePolynomial_coeff_one_ne_zero D)),
      subspacePolynomial_natDegree, ← Nat.card_eq_fintype_card, hD]
  have hbal := artinSchreier_degree_balance H _ hΛ hdne (repairedPolynomial_artinSchreier D v A l κ)
  rw [hd, hΛdeg] at hbal
  have hroots : Nat.card {x : D // H.eval (x : B) = 0} ≤ H.natDegree := by
    let f : {x : D // H.eval (x : B) = 0} → {x : B // x ∈ H.roots} :=
      fun x ↦ ⟨(x.val : B), (mem_roots hH).mpr x.property⟩
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : {x : B // x ∈ H.roots} ↦ z.val) he))
    calc
      Nat.card {x : D // H.eval (x : B) = 0} ≤ Nat.card {x : B // x ∈ H.roots} := Nat.card_le_card_of_injective f hf
      _ ≤ H.roots.card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        have he : Finset.univ.filter (fun x : B ↦ x ∈ H.roots) = H.roots.toFinset := by
          ext x; simp
        rw [he]
        exact Multiset.toFinset_card_le _
      _ ≤ H.natDegree := card_roots' H
  have hz : Nat.card {x : D // H.eval (x : B) = 0} = 2^k+2^(k-r) := by
    rw [← hzeros]
    apply Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
    rw [repairedPolynomial_eval, map_eq_zero]
  have hlow : 2^k+2^(k-r) ≤ H.natDegree := hz ▸ hroots
  refine ⟨repairedPolynomial_artinSchreier D v A l κ, hJ, hbal, hlow, ?_⟩
  have he : k+1-r = (k-r)+1 := by omega
  rw [he, pow_succ]
  rw [pow_succ] at hbal
  change 2*(repairedPolynomial D v A l κ).natDegree = 2^k*2+(tensorLinearPart D v A).natDegree at hbal
  change 2^k+2^(k-r) ≤ (repairedPolynomial D v A l κ).natDegree at hlow
  omega
/-- Remark 5.11: the additive derivative of every tensor of arbitrary positive
 rank `2r` has degree at least `N/2^r`, independently of any moment equations. -/
theorem tensorLinearPart_general_rank_degree
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (r : ℕ) (hr0 : 0 < r) (hr : tensorPolarRank D v A = 2*r) :
    2^(k+1-r) ≤ (tensorLinearPart D v A).natDegree := by
  classical
  let Q := tensorQuadraticData D v A
  let l : Module.Dual (ZMod 2) D := Subspace.dualLift Q.radical Q.radicalValue
  have hl : l ∈ Q.repairs := by
    apply (Q.mem_repairs_iff l).mpr
    intro x
    have he := LinearMap.congr_fun (Subspace.dualRestrict_comp_dualLift Q.radical) Q.radicalValue
    have hx := LinearMap.congr_fun he x
    change l (x : D) = Q.toFun (x : D) at hx
    rw [hx, CharTwo.add_self_eq_zero]
  have hdim : Module.finrank (ZMod 2) D = k+1 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm
  have hQr : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = 2*r := by
    rw [tensorQuadraticData_rank, hr]
  have hrl : 2*r ≤ k+1 := by
    have he := Q.polarMap.finrank_range_add_finrank_ker
    rw [hQr, hdim] at he
    omega
  obtain ⟨κ, hκ, _⟩ := Q.exists_bit_zeroCount_of_polarRank l hl (k+1) r (by omega) hdim hQr
  have hz : Nat.card {x : D // tensorQuadraticFunction D v A x + l x + κ = 0} = 2^k+2^(k-r) := by
    have he : k+1-r-1 = k-r := by omega
    simpa only [BinaryQuadraticData.zeroCount, Q, tensorQuadraticData, BinaryQuadraticData.toFun,
      BinaryQuadraticData.mk, Nat.add_sub_cancel, he] using hκ
  exact (repairedPolynomial_general_rank_degree D k hD v A l.toAddMonoidHom κ r hr0 hrl hr hz).2.2.2.2
/-- Lemma 5.9 in full: a nonzero moment-constrained tensor has rank at least
 `2t`, and equality gives the radical locator factorization, nonzero leading
 endpoint, exact degree, and exact radical size. -/
theorem gold_rank_degree_full
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (A : TensorCoordinates d) (hA : A ≠ (fun _ ↦ 0))
    (t : ℕ) (ht0 : 2 ≤ t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0) :
    2*t ≤ tensorPolarRank D v A ∧
      (tensorPolarRank D v A = 2*t →
        tensorLinearPart D v A = C ((tensorLinearPart D v A).coeff (2^(k+1-t))) *
          subspacePolynomial (tensorRadicalDomain D v A) ^ (2^t) ∧
        (tensorLinearPart D v A).coeff (2^(k+1-t)) ≠ 0 ∧
        (tensorLinearPart D v A).natDegree = 2^(k+1-t) ∧
        Nat.card (tensorRadicalDomain D v A) = 2^(k+1-2*t)) := by
  exact ⟨tensorPolarRank_lower_bound_of_moments D k hD v x hdual A hA t ht hM,
    fun hr ↦ tensorLinearPart_radical_factorization D k hD v A t (by omega) ht hM hr⟩
end BinaryFieldCounterexamples.Gold
