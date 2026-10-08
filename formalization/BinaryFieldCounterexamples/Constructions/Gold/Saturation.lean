/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Compression
/-!
# Sharp Gold derivative degrees and endpoint coefficients

Rank saturation gives a Frobenius root whose distinct roots exhaust its
degree. That polynomial splits and is separable. The exact upper degree and
separability at zero recover both nonzero endpoints of the Gold support
interval, with no generic-position assumption on the prescribed domain.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2]
/-- Saturating the reduced bound gives a split separable Frobenius root of exact degree. -/
theorem frobeniusRoot_saturation (t : ℕ) (P : B[X]) (S : Finset B)
    (hne : P ≠ 0) (hP : ∀ n ∈ P.support, 2^t ∣ n)
    (hd : P.natDegree ≤ S.card * 2^t)
    (hS : ∀ x ∈ S, P.eval x = 0) :
    (frobeniusRoot t P).natDegree = S.card ∧
      (frobeniusRoot t P).roots = S.val ∧
      (frobeniusRoot t P).Splits ∧ (frobeniusRoot t P).Separable := by
  classical
  have hQ : frobeniusRoot t P ≠ 0 := by
    intro h
    have he := frobeniusRoot_pow t P hP
    rw [h, zero_pow (by positivity)] at he
    exact hne he.symm
  have hQS : ∀ x ∈ S, (frobeniusRoot t P).eval x = 0 :=
    fun x hx ↦ (frobeniusRoot_eval_eq_zero_iff t P hP x).mpr (hS x hx)
  have hle := frobeniusRoot_natDegree_le t P S.card hd
  have he := roots_eq_of_natDegree_le_card_of_ne_zero hQS hle hQ
  have hedeg : (frobeniusRoot t P).natDegree = S.card := by
    apply le_antisymm hle
    have hc := card_roots' (frobeniusRoot t P)
    rwa [he] at hc
  have hs : (frobeniusRoot t P).Splits := splits_iff_card_roots.mpr (by rw [he, hedeg]; rfl)
  exact ⟨hedeg, he, hs, (nodup_roots_iff_of_splits hQ hs).mp (he ▸ S.nodup)⟩
/-- Rank saturation gives the exact number of roots in the ambient binary field. -/
theorem card_tensorLinearPart_all_zeros [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht0 : 0 < t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t) :
    Nat.card {x : B // (tensorLinearPart D v A).eval x = 0} = 2^(k+1-2*t) := by
  let e : {x : B // (tensorLinearPart D v A).eval x = 0} ≃
      {y : D // (tensorLinearPart D v A).eval (y : B) = 0} :=
    { toFun := fun x ↦ ⟨⟨x.val, tensorLinearPart_roots_mem_domain D k hD v A t ht0 ht hM hr x.val x.property⟩, x.property⟩
      invFun := fun y ↦ ⟨(y.val : B), y.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e, card_tensorLinearPart_zeros, hD, hr,
    Nat.pow_div ht (by decide : 0 < 2)]
/-- The compressed Gold derivative has the sharp degree and splits without repeated roots. -/
theorem tensorLinearPart_frobeniusRoot_saturation [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht0 : 0 < t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t) :
    (frobeniusRoot t (tensorLinearPart D v A)).natDegree = 2^(k+1-2*t) ∧
      (frobeniusRoot t (tensorLinearPart D v A)).Splits ∧
      (frobeniusRoot t (tensorLinearPart D v A)).Separable := by
  classical
  let S := Finset.univ.filter fun x : B ↦ (tensorLinearPart D v A).eval x = 0
  have hS : S.card = 2^(k+1-2*t) := by
    have he := card_tensorLinearPart_all_zeros D k hD v A t ht0 ht hM hr
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at he
    exact he
  have hne : tensorLinearPart D v A ≠ 0 := tensorLinearPart_ne_zero_of_rank_pos D v A (by omega)
  have hsupport : ∀ n ∈ (tensorLinearPart D v A).support, 2^t ∣ n := by
    intro n hn
    obtain ⟨i, rfl, hi, _⟩ := tensorLinearPart_support_interval D k hD v A t hM n hn
    exact pow_dvd_pow 2 hi
  have hd : (tensorLinearPart D v A).natDegree ≤ S.card * 2^t := by
    rw [hS, ← pow_add]
    have he : k+1-2*t+t = k+1-t := by omega
    rw [he]
    exact tensorLinearPart_natDegree_le D k hD v A t hM
  obtain ⟨hdeg, _, hsplit, hsep⟩ := frobeniusRoot_saturation t (tensorLinearPart D v A) S hne hsupport hd
    (fun x hx ↦ (Finset.mem_filter.mp hx).2)
  exact ⟨hdeg.trans hS, hsplit, hsep⟩
/-- Separability of the compressed polynomial forces the lowest allowed coefficient to be nonzero. -/
theorem coeff_ne_zero_of_frobeniusRoot_separable (t : ℕ) (P : B[X])
    (hzero : P.coeff 0 = 0) (hsep : (frobeniusRoot t P).Separable) : P.coeff (2^t) ≠ 0 := by
  have hq0 : (frobeniusRoot t P).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, frobeniusRoot, coeff_map, coeff_contract (by positivity), zero_mul, hzero, map_zero]
  have hd := hsep.eval₂_derivative_ne_zero (RingHom.id B) (by simpa using hq0)
  have hc : (frobeniusRoot t P).coeff 1 ≠ 0 := by
    simpa only [eval₂_id, ← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using hd
  intro h
  apply hc
  rw [frobeniusRoot, coeff_map, coeff_contract (by positivity), one_mul, h, map_zero]
/-- Both endpoint coefficients of the Gold support interval are genuinely nonzero. -/
theorem tensorLinearPart_endpoint_coefficients [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht0 : 0 < t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t) :
    (tensorLinearPart D v A).coeff (2^t) ≠ 0 ∧
      (tensorLinearPart D v A).natDegree = 2^(k+1-t) ∧
      (tensorLinearPart D v A).coeff (2^(k+1-t)) ≠ 0 := by
  have hsupport : ∀ n ∈ (tensorLinearPart D v A).support, 2^t ∣ n := by
    intro n hn
    obtain ⟨i, rfl, hi, _⟩ := tensorLinearPart_support_interval D k hD v A t hM n hn
    exact pow_dvd_pow 2 hi
  obtain ⟨hdeg, _, hsep⟩ := tensorLinearPart_frobeniusRoot_saturation D k hD v A t ht0 ht hM hr
  have hz : (tensorLinearPart D v A).coeff 0 = 0 := by
    by_contra h
    obtain ⟨i, hi⟩ := tensorLinearPart_support D v A 0 (mem_support_iff.mpr h)
    have : 0 < (2:ℕ)^i := by positivity
    omega
  have hlow := coeff_ne_zero_of_frobeniusRoot_separable t (tensorLinearPart D v A) hz hsep
  have hdegree : (tensorLinearPart D v A).natDegree = 2^(k+1-t) := by
    conv_lhs => rw [← frobeniusRoot_pow t _ hsupport]
    rw [natDegree_pow, hdeg, ← pow_add]
    congr 1
    omega
  refine ⟨hlow, hdegree, ?_⟩
  rw [← hdegree]
  rw [coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr (tensorLinearPart_ne_zero_of_rank_pos D v A (by omega))

end BinaryFieldCounterexamples.Gold
