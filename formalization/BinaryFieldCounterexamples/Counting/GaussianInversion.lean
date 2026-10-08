/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianIdentities
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Finite Gaussian incidence inversion

The subspace-incidence kernel has the usual explicit Gaussian Möbius inverse.
The final definitions specialize this inverse to the floor and ceiling rank
weights at Gaussian base `q²`, without encoding negative odd ranks by truncated
subtraction.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- Möbius coefficient for the finite subspace lattice. -/
def gaussianMobius (q a : ℕ) : ℚ :=
  (-1 : ℚ) ^ a * (q : ℚ) ^ (a * (a - 1) / 2)

/-- The Newton product at zero is the Gaussian Möbius coefficient. -/
theorem gaussianNewtonProduct_zero (q a : ℕ) :
    gaussianNewtonProduct q 0 a = gaussianMobius q a := by
  rw [gaussianNewtonProduct, gaussianMobius]
  simp only [zero_sub]
  calc
    ∏ x ∈ Finset.range a, -((q : ℚ) ^ x) =
        ∏ x ∈ Finset.range a, ((-1 : ℚ) * (q : ℚ) ^ x) := by
          apply Finset.prod_congr rfl
          intro x hx
          ring
    _ = (-1 : ℚ) ^ a * ∏ x ∈ Finset.range a, (q : ℚ) ^ x := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = (-1 : ℚ) ^ a * (q : ℚ) ^ (a * (a - 1) / 2) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

/-- Alternating Gaussian coefficients sum to zero away from dimension zero. -/
theorem gaussianPascal_mobius_sum (q m : ℕ) :
    ∑ a ∈ Finset.range (m + 1),
        (gaussianPascal q m a : ℚ) * gaussianMobius q a =
      if m = 0 then 1 else 0 := by
  have h := gaussianPascal_newton q m 0
  simp_rw [gaussianNewtonProduct_zero] at h
  cases m <;> simp_all

/-- Convolution of the incidence and Möbius Gaussian kernels. -/
theorem gaussianPascal_incidence_mobius (q d e u : ℕ)
    (hq : 1 < q) (heu : e ≤ u) (hud : u ≤ d) :
    ∑ a ∈ Finset.range (u - e + 1),
        gaussianMobius q a *
          (gaussianPascal q (d - e) a : ℚ) *
          gaussianPascal q (d - e - a) (u - e - a) =
      if e = u then 1 else 0 := by
  let m := u - e
  let D := d - e
  have hmD : m ≤ D := by dsimp [m, D]; omega
  have hflag (a : ℕ) (ha : a ≤ m) :
      (gaussianPascal q D a : ℚ) * gaussianPascal q (D - a) (m - a) =
        (gaussianPascal q D m : ℚ) * gaussianPascal q m a := by
    exact_mod_cast (gaussianPascal_flag q D m a hq hmD ha).symm
  calc
    ∑ a ∈ Finset.range (u - e + 1),
        gaussianMobius q a * (gaussianPascal q (d - e) a : ℚ) *
          gaussianPascal q (d - e - a) (u - e - a) =
      (gaussianPascal q D m : ℚ) *
        ∑ a ∈ Finset.range (m + 1),
          (gaussianPascal q m a : ℚ) * gaussianMobius q a := by
            dsimp [D, m]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            have hal := Finset.mem_range.mp ha
            have ham : a ≤ u - e := by omega
            have hf := hflag a (by simpa [m] using ham)
            dsimp [D, m] at hf
            calc
              gaussianMobius q a * (gaussianPascal q (d - e) a : ℚ) *
                  gaussianPascal q (d - e - a) (u - e - a) =
                gaussianMobius q a *
                  ((gaussianPascal q (d - e) a : ℚ) *
                    gaussianPascal q (d - e - a) (u - e - a)) := by ring
              _ = gaussianMobius q a *
                  ((gaussianPascal q (d - e) (u - e) : ℚ) *
                    gaussianPascal q (u - e) a) := by rw [hf]
              _ = (gaussianPascal q (d - e) (u - e) : ℚ) *
                  ((gaussianPascal q (u - e) a : ℚ) * gaussianMobius q a) := by ring
    _ = (gaussianPascal q D m : ℚ) * (if m = 0 then 1 else 0) := by
      rw [gaussianPascal_mobius_sum]
    _ = if e = u then 1 else 0 := by
      by_cases heu' : e = u
      · subst u
        simp [m, gaussianPascal_zero]
      · have hm : m ≠ 0 := by dsimp [m]; omega
        simp [heu', hm]

/-- Explicit coefficient obtained by finite Gaussian inversion.  If a rank
weight is expanded in the subspace-incidence basis, these are its unique
backward triangular coefficients. -/
def gaussianInverseCoefficient (q d e : ℕ) (w : ℕ → ℚ) : ℚ :=
  ∑ a ∈ Finset.range (d - e + 1), gaussianMobius q a *
    (gaussianPascal q (d - e) a : ℚ) * w (e + a)

/-- The minus-type rank weight, using the safe ceiling `(r+1)/2` and the
required Gaussian base `q²`. -/
def quadraticMinusRankWeight (q n t r : ℕ) : ℚ :=
  gaussianPascal (q ^ 2) (n - (r + 1) / 2) t

/-- The plus-type rank weight, using the floor `r/2` and Gaussian base `q²`. -/
def quadraticPlusRankWeight (q n t r : ℕ) : ℚ :=
  gaussianPascal (q ^ 2) (n - r / 2) t

/-- Explicit incidence coefficient for the minus-type quadratic rank weight. -/
def quadraticMinusIncidenceCoefficient (q d n t e : ℕ) : ℚ :=
  gaussianInverseCoefficient q d e (quadraticMinusRankWeight q n t)

/-- Explicit incidence coefficient for the plus-type quadratic rank weight. -/
def quadraticPlusIncidenceCoefficient (q d n t e : ℕ) : ℚ :=
  gaussianInverseCoefficient q d e (quadraticPlusRankWeight q n t)

end BinaryFieldCounterexamples
