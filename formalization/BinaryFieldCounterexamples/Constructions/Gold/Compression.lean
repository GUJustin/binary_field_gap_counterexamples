/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HighMoments
public import BinaryFieldCounterexamples.Agreement.Basic
public import BinaryFieldCounterexamples.Constructions.Gold.Polar
/-!
# Frobenius compression and Gold root saturation

Contracting exponents and applying inverse Frobenius to coefficients gives
an actual power root of every polynomial with divisible support. This yields
the sharper distinct-root bound needed for the Gold additive derivative.
At polar rank `2t`, its roots already present in the prescribed domain
saturate that bound, so no further field roots can occur outside the domain.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2]
/-- Contract exponents and take inverse Frobenius on coefficients. -/
noncomputable def frobeniusRoot (t : ℕ) (P : B[X]) : B[X] :=
  (P.contract (2^t)).map (iterateFrobeniusEquiv B 2 t).symm.toRingHom
/-- Divisible support makes exponent contraction inverse to expansion. -/
theorem expand_contract_of_support_dvd {B : Type*} [Field B] (t : ℕ) (P : B[X])
    (hP : ∀ n ∈ P.support, 2^t ∣ n) :
    expand B (2^t) (P.contract (2^t)) = P := by
  ext n
  rw [coeff_expand (by positivity), coeff_contract (by positivity)]
  by_cases hn : 2^t ∣ n
  · simp only [hn, ↓reduceIte, Nat.div_mul_cancel hn]
  · simp only [hn, ↓reduceIte]
    by_contra h
    exact hn (hP n (mem_support_iff.mpr (Ne.symm h)))
/-- The contracted inverse-Frobenius polynomial is an actual power root. -/
theorem frobeniusRoot_pow (t : ℕ) (P : B[X])
    (hP : ∀ n ∈ P.support, 2^t ∣ n) : frobeniusRoot t P ^ (2^t) = P := by
  rw [frobeniusRoot, ← map_iterateFrobenius_expand 2, ← map_expand, map_map]
  have he : (iterateFrobenius B 2 t).comp (iterateFrobeniusEquiv B 2 t).symm.toRingHom =
      RingHom.id B := by
    ext x
    exact (iterateFrobeniusEquiv B 2 t).apply_symm_apply x
  rw [he, map_id, expand_contract_of_support_dvd t P hP]
/-- Exponent contraction divides the degree bound by its known factor. -/
theorem frobeniusRoot_natDegree_le (t : ℕ) (P : B[X]) (m : ℕ)
    (hP : P.natDegree ≤ m * 2^t) : (frobeniusRoot t P).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [frobeniusRoot, coeff_map, coeff_contract (by positivity),
    coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.mul_lt_mul_of_pos_right hn (by positivity))),
    map_zero]
/-- Taking the Frobenius root preserves the exact set of field roots. -/
theorem frobeniusRoot_eval_eq_zero_iff (t : ℕ) (P : B[X])
    (hP : ∀ n ∈ P.support, 2^t ∣ n) (x : B) :
    (frobeniusRoot t P).eval x = 0 ↔ P.eval x = 0 := by
  conv_rhs => rw [← frobeniusRoot_pow t P hP, eval_pow, pow_eq_zero_iff (by positivity : 2^t ≠ 0)]
/-- A nonzero polynomial with Frobenius-divisible support has the reduced root bound. -/
theorem card_filter_roots_le_of_support_dvd [DecidableEq B] (t : ℕ) (P : B[X]) (m : ℕ) (S : Finset B)
    (hne : P ≠ 0) (hP : ∀ n ∈ P.support, 2^t ∣ n)
    (hd : P.natDegree ≤ m * 2^t) : (S.filter fun x ↦ P.eval x = 0).card ≤ m := by
  classical
  have hroot : frobeniusRoot t P ≠ 0 := by
    intro h
    have he := frobeniusRoot_pow t P hP
    rw [h, zero_pow (by positivity)] at he
    exact hne he.symm
  have he : S.filter (fun x ↦ P.eval x = 0) =
      S.filter (fun x ↦ (frobeniusRoot t P).eval x = 0) := by
    ext x
    simp only [Finset.mem_filter, frobeniusRoot_eval_eq_zero_iff t P hP]
  rw [he]
  exact (card_filter_eval_eq_zero_le S _ hroot).trans (frobeniusRoot_natDegree_le t P m hd)
/-- Gold moment vanishing gives the sharp reduced bound on roots in any finite subset of the field. -/
theorem card_tensorLinearPart_roots_le [Algebra (ZMod 2) B] [DecidableEq B]
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hne : tensorLinearPart D v A ≠ 0) (S : Finset B) :
    (S.filter fun x ↦ (tensorLinearPart D v A).eval x = 0).card ≤ 2^(k+1-2*t) := by
  apply card_filter_roots_le_of_support_dvd t _ _ _ hne
  · intro n hn
    obtain ⟨i, rfl, hi, _⟩ := tensorLinearPart_support_interval D k hD v A t hM n hn
    exact pow_dvd_pow 2 hi
  · have he : k+1-t = (k+1-2*t)+t := by omega
    simpa only [he, pow_add] using tensorLinearPart_natDegree_le D k hD v A t hM

/-- Positive polar rank forces a nonzero additive derivative. -/
theorem tensorLinearPart_ne_zero_of_rank_pos [Algebra (ZMod 2) B]
    (D : AddSubgroup B) {d : ℕ} (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (hr : 0 < tensorPolarRank D v A) : tensorLinearPart D v A ≠ 0 := by
  intro h
  have hm : tensorPolarMap D v A = 0 := by
    ext y x
    have hy : tensorPolarFunctional D v A y = 0 :=
      (tensorPolarFunctional_eq_zero_iff D v A y).mpr (by rw [h]; simp)
    exact congrArg (fun l : D →+ ZMod 2 ↦ l x) hy
  unfold tensorPolarRank at hr
  rw [hm, LinearMap.range_zero, finrank_bot] at hr
  omega

/-- Saturation of the reduced root bound forces every field root of J into the prescribed domain. -/
theorem tensorLinearPart_roots_mem_domain [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D = 2^(k+1)) {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d)
    (t : ℕ) (ht0 : 0 < t) (ht : 2*t ≤ k+1)
    (hM : ∀ r, 1 ≤ r → r < t → goldMoment D v A r = 0)
    (hr : tensorPolarRank D v A = 2*t)
    (x : B) (hx : (tensorLinearPart D v A).eval x = 0) : x ∈ D := by
  classical
  let J := tensorLinearPart D v A
  have hne : J ≠ 0 := tensorLinearPart_ne_zero_of_rank_pos D v A (by omega)
  have hbound : Fintype.card {x : B // J.eval x = 0} ≤ 2^(k+1-2*t) := by
    rw [Fintype.card_subtype]
    exact card_tensorLinearPart_roots_le D k hD v A t ht hM hne Finset.univ
  have heq : Fintype.card {y : D // J.eval (y : B) = 0} = 2^(k+1-2*t) := by
    rw [← Nat.card_eq_fintype_card, card_tensorLinearPart_zeros, hD, hr,
      Nat.pow_div ht (by decide : 0 < 2)]
  let f : {y : D // J.eval (y : B) = 0} → {x : B // J.eval x = 0} :=
    fun y ↦ ⟨(y.val : B), y.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {x : B // J.eval x = 0} ↦ z.val) hab
  by_contra hnot
  have hns : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
    have he : (y.val : B) = x := congrArg Subtype.val hy
    exact hnot (he ▸ y.val.property)
  have hlt := Fintype.card_lt_of_injective_not_surjective f hf hns
  omega

end BinaryFieldCounterexamples.Gold
