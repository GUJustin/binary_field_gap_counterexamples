/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.MomentKernel
/-!
# Exact dimension arithmetic for the Gold moment code

The parity correction and natural subtractions are justified before converting
rank-nullity to the two factors used in the minimum-rank population bound.
This module does not assume or prove that remaining population inequality.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
/-- Dimension of alternating matrices, with the manuscript parity correction. -/
theorem alternating_dimension (d : ℕ) :
    d.choose 2 = (d - if Even d then 1 else 0) * (d/2) := by
  rw [Nat.choose_two_right]
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    have he : (n+n)/2=n := by omega
    rw [he]
    rw [show (n+n)*(n+n-1) = ((n+n-1)*n)*2 by ring]
    omega
  · have hm : d % 2 = 1 := by
      by_contra hn
      have hz : d%2=0 := by omega
      exact h (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hz))
    have he : d=2*(d/2)+1 := by omega
    have hs : d-1=2*(d/2) := by omega
    rw [hs, show d*(2*(d/2)) = (d*(d/2))*2 by ring]
    simp
/-- The positive `Δ` hypothesis prevents truncation in the dimension identity. -/
theorem moment_dimension_decomposition (m d t : ℕ)
    (hdm : d ≤ m) (ht : t ≤ d/2) (htpos : 1 ≤ t)
    (hΔ : 1 ≤ m-t*(m-d+if Even d then 1 else 0)) :
    d.choose 2 - m*(t-1) =
      (d-if Even d then 1 else 0)*(d/2-t) +
        (m-t*(m-d+if Even d then 1 else 0)) := by
  rw [alternating_dimension]
  have hd : 2 ≤ d := by omega
  have hi : (if Even d then 1 else 0) ≤ d := by split_ifs <;> omega
  have hr : t*(m-d+if Even d then 1 else 0) ≤ m := by omega
  have hsum : (d-if Even d then 1 else 0)+(m-d+if Even d then 1 else 0)=m := by
    omega
  -- Split the ambient dimension into the retained part and its complement.
  have hbalance : m*(t-1)+(m-t*(m-d+if Even d then 1 else 0)) =
      (d-if Even d then 1 else 0)*t := by
    apply Nat.add_right_cancel (m := t*(m-d+if Even d then 1 else 0))
    calc
      _ = m*(t-1)+m := by rw [Nat.add_assoc, Nat.sub_add_cancel hr]
      _ = m*((t-1)+1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = m*t := by rw [Nat.sub_add_cancel htpos]
      _ = ((d-if Even d then 1 else 0)+(m-d+if Even d then 1 else 0))*t := by
        rw [hsum]
      _ = _ := by rw [Nat.add_mul, Nat.mul_comm (m-d+if Even d then 1 else 0) t]
  have hsplit : (d-if Even d then 1 else 0)*(d/2) =
      (d-if Even d then 1 else 0)*t+(d-if Even d then 1 else 0)*(d/2-t) := by
    rw [←Nat.mul_add, Nat.add_comm t (d/2-t), Nat.sub_add_cancel ht]
  have he : (d-if Even d then 1 else 0)*(d/2) =
      m*(t-1) + (d-if Even d then 1 else 0)*(d/2-t) +
        (m-t*(m-d+if Even d then 1 else 0)) := by
    rw [hsplit, ←hbalance]
    ac_rfl
  rw [he, Nat.add_assoc, Nat.add_sub_cancel_left]
/-- The concrete moment kernel is large enough for the eventual rank-distribution
inequality, with both binary powers keeping their exact exponents. -/
theorem goldMomentKernel_card_lower_bound_delta
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) {d : ℕ} (v : Fin d → parameterDomain D)
    (t m : ℕ) (hB : Fintype.card B=2^m)
    (hdm : d ≤ m) (ht : t ≤ d/2) (htpos : 1 ≤ t)
    (hΔ : 1 ≤ m-t*(m-d+if Even d then 1 else 0)) :
    2^((d-if Even d then 1 else 0)*(d/2-t)) *
      2^(m-t*(m-d+if Even d then 1 else 0)) ≤
        Nat.card (goldMomentKernel D v t) := by
  have h := goldMomentKernel_card_lower_bound D v t m hB
  rw [moment_dimension_decomposition m d t hdm ht htpos hΔ, pow_add] at h
  exact h
end BinaryFieldCounterexamples.Gold
