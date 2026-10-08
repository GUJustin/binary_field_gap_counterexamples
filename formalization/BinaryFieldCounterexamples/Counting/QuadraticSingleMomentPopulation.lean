/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.QuadraticCodeIncidence

/-!
# Minimum-rank population from one positive moment

At the complementary Gaussian index, a family with minimum rank `2t` has only
its zero element and exact minimum-rank layer left in the ceiling-rank moment.
The actual Fourier lower bound therefore gives the required population bound
without a second dual moment.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Number of elements in a finite family having the specified numerical rank. -/
def exactRankPopulation {C : Type*} [Fintype C] (rank : C → ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun x => rank x=r)).card

/-- At the complementary Gaussian index, a minimum-rank family contributes
only its zero element and its exact minimum-rank layer. -/
theorem gaussianCeilRankSum_collapse {C : Type*} [Fintype C] [Zero C]
    (q n t : ℕ) (rank : C → ℕ) (hq : 1 < q) (ht0 : 0 < t) (htn : t ≤ n)
    (hr0 : rank 0=0) (hmin : ∀ x, x≠0 → 2*t ≤ rank x)
    (hmax : ∀ x, rank x ≤ 2*n) :
    (∑ x : C, (gaussianPascal (q^2) (n-(rank x+1)/2) (n-t) : ℚ)) =
      (gaussianPascal (q^2) n t : ℚ) + exactRankPopulation rank (2*t) := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  have hpoint (x : C) :
      (gaussianPascal (q^2) (n-(rank x+1)/2) (n-t) : ℚ) =
        if x=0 then (gaussianPascal (q^2) n t : ℚ)
        else if rank x=2*t then 1 else 0 := by
    by_cases hx : x=0
    · subst x
      rw [ite_eq_left rfl, hr0]
      norm_num only [zero_add, Nat.reduceDiv, Nat.sub_zero]
      exact_mod_cast (gaussianPascal_symm (q^2) n t hq2 htn).symm
    · rw [ite_eq_right hx]
      by_cases heq : rank x=2*t
      · rw [ite_eq_left heq, heq]
        have he : (2*t+1)/2=t := by omega
        rw [he, gaussianPascal_self]
        norm_num
      · rw [ite_eq_right heq]
        have hgt : 2*t<rank x := lt_of_le_of_ne (hmin x hx) (Ne.symm heq)
        have hceil : t<(rank x+1)/2 := by
          apply (Nat.lt_div_iff_mul_lt (by decide : 0<2)).mpr
          omega
        have hceilmax : (rank x+1)/2 ≤ n := by
          apply (Nat.div_le_iff_le_mul (by decide : 0<2)).mpr
          have := hmax x
          omega
        rw [gaussianPascal_eq_zero (q^2) (n-(rank x+1)/2) (n-t) (by omega)]
        norm_num
  calc
    (∑ x : C, (gaussianPascal (q^2) (n-(rank x+1)/2) (n-t) : ℚ)) =
      ∑ x : C, (if x=0 then (gaussianPascal (q^2) n t : ℚ)
        else if rank x=2*t then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hpoint x
    _ = (gaussianPascal (q^2) n t : ℚ) + exactRankPopulation rank (2*t) := by
      have hp (x : C) :
          (if x=0 then (gaussianPascal (q^2) n t : ℚ)
            else if rank x=2*t then 1 else 0) =
          (if x=0 then (gaussianPascal (q^2) n t : ℚ) else 0) +
            (if rank x=2*t then 1 else 0) := by
        by_cases hx : x=0
        · subst x
          rw [ite_eq_left rfl]
          simp [hr0]
          omega
        · rw [ite_eq_right hx]
          simp [hx]
      calc
        _ = (∑ x : C, if x=0 then (gaussianPascal (q^2) n t : ℚ) else 0) +
            ∑ x : C, if rank x=2*t then 1 else 0 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              exact hp x
        _ = _ := by simp [exactRankPopulation]

/-- A single positive Fourier moment already lower-bounds the exact minimum
rank population. -/
theorem minimumPopulation_lower_of_single_moment
    (q t : ℕ) (G H M X : ℝ) (hH : 0 < H)
    (hM : M=H*(q^t : ℕ)) (hmoment : G*M ≤ H*(G+X)) :
    (((q^t : ℕ) : ℝ)-1)*G ≤ X := by
  rw [hM] at hmoment
  apply le_of_mul_le_mul_left _ hH
  linarith

end BinaryFieldCounterexamples
