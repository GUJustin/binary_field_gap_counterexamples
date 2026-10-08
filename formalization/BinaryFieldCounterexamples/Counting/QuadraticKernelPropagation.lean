/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicKernelStep
public import BinaryFieldCounterexamples.Counting.GaussianFourierTransform
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Weighted propagation through a hyperbolic plane

The grouped inverse-incidence recurrences are diagonalized by the Gaussian
weighted transform.  The `A` transform acquires a factor `q^(2s)`, while the
`B` transform acquires the additional type factor `q`.
-/

@[expose] public section


namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators

/-- Casting a square base commutes with taking powers. -/
theorem quadraticKernel_q_sq_pow (q u : ℕ) : (((q^2 : ℕ) : ℚ)^u) = (q : ℚ)^(2*u) := by
  norm_num only [Nat.cast_pow]
  rw [← pow_mul]

/-- A hyperbolic plane multiplies the weighted `A` transform by `q^(2s)`. -/
theorem groupedRankKernelA_weight_step (q n s : ℕ) (hq : 1 < q) (hs : s ≤ n+1)
    (K L : ℕ → ℚ) (h0 : L 0 = K 0)
    (h1 : L 1 = (q : ℚ) * K 1 + ((q : ℚ)-1) * K 0)
    (hstep : ∀ r, L (r+2) = (q : ℚ)^(r+2) * K (r+2) +
      ((q : ℚ)-1) * (q : ℚ)^(r+1) * K (r+1) - (q : ℚ)^(r+1) * K r) :
    gaussianWeightedSum (q^2) (n+1) s (groupedRankKernelA L) =
      (q : ℚ)^(2*s) * gaussianWeightedSum (q^2) n s (groupedRankKernelA K) := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  rw [gaussianWeightedSum_rank_step (q^2) n s hq2 hs
    (groupedRankKernelA K) (groupedRankKernelA L)]
  · rw [quadraticKernel_q_sq_pow]
  · simpa [groupedRankKernelA] using h0
  · intro u
    rw [groupedRankKernelA_step q K L h1 hstep u]
    rw [quadraticKernel_q_sq_pow, quadraticKernel_q_sq_pow]
    rw [show 2*(u+1)=2*u+2 by ring]

/-- A hyperbolic plane multiplies the weighted `B` transform by `q^(2s+1)`. -/
theorem groupedRankKernelB_weight_step (q n s : ℕ) (hq : 1 < q) (hs : s ≤ n+1)
    (K L : ℕ → ℚ) (h0 : L 0 = K 0)
    (h1 : L 1 = (q : ℚ) * K 1 + ((q : ℚ)-1) * K 0)
    (hstep : ∀ r, L (r+2) = (q : ℚ)^(r+2) * K (r+2) +
      ((q : ℚ)-1) * (q : ℚ)^(r+1) * K (r+1) - (q : ℚ)^(r+1) * K r) :
    gaussianWeightedSum (q^2) (n+1) s (groupedRankKernelB L) =
      (q : ℚ)^(2*s+1) * gaussianWeightedSum (q^2) n s (groupedRankKernelB K) := by
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by omega) hq
  let P : ℕ → ℚ := fun u => (q : ℚ) * groupedRankKernelB K u
  have hP0 : groupedRankKernelB L 0 = P 0 := by
    dsimp [P]
    exact groupedRankKernelB_zero q K L h0 h1
  have hPs (u : ℕ) : groupedRankKernelB L (u+1) =
      (((q^2 : ℕ) : ℚ)^(u+1)) * P (u+1) - (((q^2 : ℕ) : ℚ)^u) * P u := by
    rw [groupedRankKernelB_step q K L hstep u]
    dsimp [P]
    rw [quadraticKernel_q_sq_pow, quadraticKernel_q_sq_pow]
    ring
  rw [gaussianWeightedSum_rank_step (q^2) n s hq2 hs P
    (groupedRankKernelB L) hP0 hPs]
  have hscale : gaussianWeightedSum (q^2) n s P =
      (q : ℚ) * gaussianWeightedSum (q^2) n s (groupedRankKernelB K) := by
    unfold gaussianWeightedSum P
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hscale, quadraticKernel_q_sq_pow]
  ring


/-- A Gaussian weighted sum above its ambient range vanishes when the sequence does. -/
theorem gaussianWeightedSum_eq_zero_of_tail (Q n s : ℕ) (P : ℕ → ℚ)
    (hns : n < s) (hP : ∀ u, n < u → P u = 0) :
    gaussianWeightedSum Q n s P = 0 := by
  unfold gaussianWeightedSum
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hun : u ≤ n
  · rw [show gaussianBinomial Q (n-u) (s-u) = 0 by
      simp [gaussianBinomial, show ¬s-u ≤ n-u by omega]]
    simp
  · rw [hP u (by omega)]
    ring

/-- Repeated hyperbolic planes multiply the weighted `A` transform by `q^(2rs)`. -/
theorem groupedRankKernelA_weight_iterate (q n : ℕ) (hq : 1 < q)
    (K : ℕ → ℕ → ℚ)
    (h0 : ∀ r, K (r+1) 0 = K r 0)
    (h1 : ∀ r, K (r+1) 1 = (q : ℚ) * K r 1 + ((q : ℚ)-1) * K r 0)
    (hstep : ∀ r j, K (r+1) (j+2) = (q : ℚ)^(j+2) * K r (j+2) +
      ((q : ℚ)-1) * (q : ℚ)^(j+1) * K r (j+1) - (q : ℚ)^(j+1) * K r j)
    (htail : ∀ r u, n+r < u → groupedRankKernelA (K r) u = 0)
    (r s : ℕ) (hs : s ≤ n+r) :
    gaussianWeightedSum (q^2) (n+r) s (groupedRankKernelA (K r)) =
      (q : ℚ)^(2*r*s) * gaussianWeightedSum (q^2) n s (groupedRankKernelA (K 0)) := by
  induction r generalizing s with
  | zero => simp
  | succ r ih =>
      rw [show n+(r+1)=(n+r)+1 by omega,
        groupedRankKernelA_weight_step q (n+r) s hq (by omega)
          (K r) (K (r+1)) (h0 r) (h1 r) (hstep r)]
      by_cases hsr : s ≤ n+r
      · rw [ih s hsr]
        calc
          (q : ℚ)^(2*s) * ((q : ℚ)^(2*r*s) *
              gaussianWeightedSum (q^2) n s (groupedRankKernelA (K 0))) =
            (q : ℚ)^(2*s+2*r*s) *
              gaussianWeightedSum (q^2) n s (groupedRankKernelA (K 0)) := by
                rw [pow_add]
                ring
          _ = _ := by congr 2; ring
      · have he : s=n+r+1 := by omega
        subst s
        rw [gaussianWeightedSum_above, htail r (n+r+1) (by omega)]
        have hb : gaussianWeightedSum (q^2) n (n+r+1) (groupedRankKernelA (K 0))=0 := by
          apply gaussianWeightedSum_eq_zero_of_tail
          · omega
          · intro u hu
            exact htail 0 u (by simpa using hu)
        rw [hb]
        ring

/-- Repeated hyperbolic planes multiply the weighted `B` transform by `q^(r(2s+1))`. -/
theorem groupedRankKernelB_weight_iterate (q n : ℕ) (hq : 1 < q)
    (K : ℕ → ℕ → ℚ)
    (h0 : ∀ r, K (r+1) 0 = K r 0)
    (h1 : ∀ r, K (r+1) 1 = (q : ℚ) * K r 1 + ((q : ℚ)-1) * K r 0)
    (hstep : ∀ r j, K (r+1) (j+2) = (q : ℚ)^(j+2) * K r (j+2) +
      ((q : ℚ)-1) * (q : ℚ)^(j+1) * K r (j+1) - (q : ℚ)^(j+1) * K r j)
    (htail : ∀ r u, n+r < u → groupedRankKernelB (K r) u = 0)
    (r s : ℕ) (hs : s ≤ n+r) :
    gaussianWeightedSum (q^2) (n+r) s (groupedRankKernelB (K r)) =
      (q : ℚ)^(r*(2*s+1)) * gaussianWeightedSum (q^2) n s (groupedRankKernelB (K 0)) := by
  induction r generalizing s with
  | zero => simp
  | succ r ih =>
      rw [show n+(r+1)=(n+r)+1 by omega,
        groupedRankKernelB_weight_step q (n+r) s hq (by omega)
          (K r) (K (r+1)) (h0 r) (h1 r) (hstep r)]
      by_cases hsr : s ≤ n+r
      · rw [ih s hsr]
        calc
          (q : ℚ)^(2*s+1) * ((q : ℚ)^(r*(2*s+1)) *
              gaussianWeightedSum (q^2) n s (groupedRankKernelB (K 0))) =
            (q : ℚ)^((2*s+1)+r*(2*s+1)) *
              gaussianWeightedSum (q^2) n s (groupedRankKernelB (K 0)) := by
                rw [pow_add]
                ring
          _ = _ := by congr 2; ring
      · have he : s=n+r+1 := by omega
        subst s
        rw [gaussianWeightedSum_above, htail r (n+r+1) (by omega)]
        have hb : gaussianWeightedSum (q^2) n (n+r+1) (groupedRankKernelB (K 0))=0 := by
          apply gaussianWeightedSum_eq_zero_of_tail
          · omega
          · intro u hu
            exact htail 0 u (by simpa using hu)
        rw [hb]
        ring

end BinaryFieldCounterexamples.QuadraticGeometry
