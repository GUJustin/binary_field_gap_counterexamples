/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.QuadraticKernelPropagation
public import BinaryFieldCounterexamples.Counting.QuadraticRankOneWeight
public import BinaryFieldCounterexamples.Counting.SymmetricZeroKernel
public import BinaryFieldCounterexamples.Counting.AnisotropicWeightedBase
import Mathlib.Tactic.Ring

/-!
# Weighted quadratic kernels in every rank

The zero, rank-one, and anisotropic-plane bases are propagated through an
arbitrary proved chain of hyperbolic extensions.  The resulting formulas keep
the exact Gaussian factor and the sign distinguishing the two even types.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open scoped BigOperators
open QuadraticGeometry

/-- The rank-one base has the exact lower grouped weighted transform. -/
theorem rankOneIncidenceKernel_weightedA (q b j : ℕ) (hq : 1 < q)
    (hj : j < b) :
    gaussianWeightedSum (q^2) b j
      (groupedRankKernelA (rankOneIncidenceKernel q b)) =
      (q : ℚ)^((2*b+1)*j) * (gaussianPascal (q^2) (b-1) j : ℚ) := by
  let t := b-j
  have ht0 : 0 < t := by dsimp [t]; omega
  have htb : t ≤ b := by dsimp [t]; omega
  rw [show j=b-t by dsimp [t]; omega]
  have h := rankOneGroupedKernel_weightedSum q b t hq ht0 htb
  rw [← h]
  unfold gaussianWeightedSum
  apply Finset.sum_congr rfl
  intro u hu
  have huj : u ≤ b-t := by simpa using Finset.mem_range.mp hu
  rw [gaussianBinomial_eq_gaussianPascal (q^2) (b-u) (b-t-u)
    (Nat.one_lt_pow (by omega) hq)]
  have hs := gaussianPascal_symm (q^2) (b-u) (b-t-u)
    (Nat.one_lt_pow (by omega) hq) (by omega)
  rw [show b-u-(b-t-u)=t by omega] at hs
  rw [hs]
  congr 1
  unfold groupedRankKernelA rankOneGroupedKernelA
  split <;> rfl

/-- The rank-one base has zero upper grouped weighted transform. -/
theorem rankOneIncidenceKernel_weightedB (q b j : ℕ) (hq : 1 < q)
    (hj : j < b) :
    gaussianWeightedSum (q^2) b j
      (groupedRankKernelB (rankOneIncidenceKernel q b)) = 0 := by
  unfold gaussianWeightedSum
  apply Finset.sum_eq_zero
  intro u hu
  change (gaussianBinomial (q^2) (b-u) (j-u) : ℚ) *
    rankOneGroupedKernelB q b u = 0
  rw [rankOneGroupedKernelB_eq_zero q b u hq (by
    have : u < j+1 := Finset.mem_range.mp hu
    omega)]
  ring

/-- A sequence of raw kernels obtained by adjoining hyperbolic planes. -/
def HyperbolicKernelChain (q b : ℕ) (K : ℕ → ℕ → ℚ) : Prop :=
  (∀ r, K (r+1) 0 = K r 0) ∧
  (∀ r, K (r+1) 1 = (q : ℚ) * K r 1 + ((q : ℚ)-1) * K r 0) ∧
  (∀ r j, K (r+1) (j+2) = (q : ℚ)^(j+2) * K r (j+2) +
    ((q : ℚ)-1) * (q : ℚ)^(j+1) * K r (j+1) -
      (q : ℚ)^(j+1) * K r j) ∧
  (∀ r u, b+r < u → groupedRankKernelA (K r) u = 0) ∧
  (∀ r u, b+r < u → groupedRankKernelB (K r) u = 0)

theorem hyperbolicKernelChain_weightedA (q b r j : ℕ) (hq : 1 < q)
    (K : ℕ → ℕ → ℚ) (hK : HyperbolicKernelChain q b K)
    (hj : j ≤ b+r) :
    gaussianWeightedSum (q^2) (b+r) j (groupedRankKernelA (K r)) =
      (q : ℚ)^(2*r*j) *
        gaussianWeightedSum (q^2) b j (groupedRankKernelA (K 0)) := by
  exact groupedRankKernelA_weight_iterate q b hq K hK.1 hK.2.1 hK.2.2.1
    hK.2.2.2.1 r j hj

theorem hyperbolicKernelChain_weightedB (q b r j : ℕ) (hq : 1 < q)
    (K : ℕ → ℕ → ℚ) (hK : HyperbolicKernelChain q b K)
    (hj : j ≤ b+r) :
    gaussianWeightedSum (q^2) (b+r) j (groupedRankKernelB (K r)) =
      (q : ℚ)^(r*(2*j+1)) *
        gaussianWeightedSum (q^2) b j (groupedRankKernelB (K 0)) := by
  exact groupedRankKernelB_weight_iterate q b hq K hK.1 hK.2.1 hK.2.2.1
    hK.2.2.2.2 r j hj

/-- Starting with an even-dimensional zero form and adjoining `s` hyperbolic
planes gives the positive even weighted `A` evaluation. -/
theorem positiveEvenKernelChain_weightedA (q n s j : ℕ) (hq : 1 < q)
    (hsn : s ≤ n) (hj : j ≤ n-s) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = zeroQuadraticKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelA (K s)) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) (n-s) j : ℚ) := by
  rw [hyperbolicKernelChain_weightedA q (n-s) s j hq K hK (by omega), hbase,
    zeroQuadraticKernel_weightedA q (n-s) j hq hj]
  have hc : 2*s+(2*(n-s)+1)=2*n+1 := by omega
  have hex : 2*s*j+(2*(n-s)+1)*j=(2*n+1)*j := by
    calc
      _ = (2*s+(2*(n-s)+1))*j := by ring
      _ = _ := by rw [hc]
  rw [← mul_assoc, ← pow_add, hex]

/-- The corresponding positive-even `B` evaluation records the quadratic
type sign and its exact power of `q`. -/
theorem positiveEvenKernelChain_weightedB (q n s j : ℕ) (hq : 1 < q)
    (hsn : s ≤ n) (hj : j ≤ n-s) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = zeroQuadraticKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelB (K s)) =
      (q : ℚ)^((2*n-1)*j+2*n-s) *
        (gaussianPascal (q^2) (n-s) j : ℚ) := by
  rw [hyperbolicKernelChain_weightedB q (n-s) s j hq K hK (by omega), hbase,
    zeroQuadraticKernel_weightedB q (n-s) j hq hj]
  by_cases hm : n-s=0
  · have hj0 : j=0 := by omega
    have hns : n=s := by omega
    subst j
    have hex : s*(2*0+1)+(2*(n-s)+(2*(n-s)-1)*0)=
        (2*n-1)*0+2*n-s := by omega
    rw [← mul_assoc, ← pow_add, hex]
  · have hm0 : 0<n-s := Nat.pos_of_ne_zero hm
    have hc : 2*s+(2*(n-s)-1)=2*n-1 := by omega
    have hc0 : s+2*(n-s)=2*n-s := by omega
    have hex : s*(2*j+1)+(2*(n-s)+(2*(n-s)-1)*j)=
        (2*n-1)*j+2*n-s := by
      calc
        _ = (2*s+(2*(n-s)-1))*j+(s+2*(n-s)) := by ring
        _ = _ := by rw [hc,hc0]; omega
    rw [← mul_assoc, ← pow_add, hex]

/-- Starting with a rank-one form and adjoining `s` hyperbolic planes gives
the exact odd-rank lower weighted evaluation. -/
theorem oddKernelChain_weightedA (q n s j : ℕ) (hq : 1 < q)
    (hsn : s < n) (hj : j < n-s) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = rankOneIncidenceKernel q (n-s)) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelA (K s)) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) (n-s-1) j : ℚ) := by
  rw [hyperbolicKernelChain_weightedA q (n-s) s j hq K hK (by omega), hbase,
    rankOneIncidenceKernel_weightedA q (n-s) j hq hj]
  have hc : 2*s+(2*(n-s)+1)=2*n+1 := by omega
  have hex : 2*s*j+(2*(n-s)+1)*j=(2*n+1)*j := by
    calc
      _ = (2*s+(2*(n-s)+1))*j := by ring
      _ = _ := by rw [hc]
  rw [← mul_assoc, ← pow_add, hex]

/-- Every odd-rank upper grouped transform vanishes. -/
theorem oddKernelChain_weightedB (q n s j : ℕ) (hq : 1 < q)
    (_hsn : s < n) (hj : j < n-s) (K : ℕ → ℕ → ℚ)
    (hK : HyperbolicKernelChain q (n-s) K)
    (hbase : K 0 = rankOneIncidenceKernel q (n-s)) :
    gaussianWeightedSum (q^2) ((n-s)+s) j (groupedRankKernelB (K s)) = 0 := by
  rw [hyperbolicKernelChain_weightedB q (n-s) s j hq K hK (by omega), hbase,
    rankOneIncidenceKernel_weightedB q (n-s) j hq hj]
  ring

/-- Starting with the anisotropic plane over an even radical and adjoining
the remaining hyperbolic planes gives the negative even `A` evaluation. -/
theorem negativeEvenKernelChain_weightedA (q n s j : ℕ) (hq : 1 < q)
    (hs0 : 0 < s) (hsn : s ≤ n) (hj : j ≤ n-s)
    (K : ℕ → ℕ → ℚ) (hK : HyperbolicKernelChain q (n-s+1) K)
    (hbase : K 0 = anisotropicPlaneKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s+1)+(s-1)) j
        (groupedRankKernelA (K (s-1))) =
      (q : ℚ)^((2*n+1)*j) * (gaussianPascal (q^2) (n-s) j : ℚ) := by
  rw [hyperbolicKernelChain_weightedA q (n-s+1) (s-1) j hq K hK (by omega), hbase,
    anisotropicPlaneKernel_weightedA q (n-s) j hq hj]
  have hc : 2*(s-1)+(2*(n-s)+3)=2*n+1 := by omega
  have hex : 2*(s-1)*j+(2*(n-s)+3)*j=(2*n+1)*j := by
    calc
      _ = (2*(s-1)+(2*(n-s)+3))*j := by ring
      _ = _ := by rw [hc]
  rw [← mul_assoc, ← pow_add, hex]

/-- The negative even `B` evaluation has the opposite type sign. -/
theorem negativeEvenKernelChain_weightedB (q n s j : ℕ) (hq : 1 < q)
    (hs0 : 0 < s) (hsn : s ≤ n) (hj : j ≤ n-s)
    (K : ℕ → ℕ → ℚ) (hK : HyperbolicKernelChain q (n-s+1) K)
    (hbase : K 0 = anisotropicPlaneKernel q (2*(n-s))) :
    gaussianWeightedSum (q^2) ((n-s+1)+(s-1)) j
        (groupedRankKernelB (K (s-1))) =
      -(q : ℚ)^((2*n-1)*j+2*n-s) *
        (gaussianPascal (q^2) (n-s) j : ℚ) := by
  rw [hyperbolicKernelChain_weightedB q (n-s+1) (s-1) j hq K hK (by omega), hbase,
    anisotropicPlaneKernel_weightedB q (n-s) j hq hj]
  have hc : 2*(s-1)+(2*(n-s)+1)=2*n-1 := by omega
  have hc0 : (s-1)+(2*(n-s)+1)=2*n-s := by omega
  have hex : (s-1)*(2*j+1)+(2*(n-s)+1)*(j+1)=
      (2*n-1)*j+2*n-s := by
    calc
      _ = (2*(s-1)+(2*(n-s)+1))*j+((s-1)+(2*(n-s)+1)) := by ring
      _ = _ := by rw [hc,hc0]; omega
  calc
    _ = -((q : ℚ)^((s-1)*(2*j+1)) *
          (q : ℚ)^((2*(n-s)+1)*(j+1))) *
          (gaussianPascal (q^2) (n-s) j : ℚ) := by ring
    _ = _ := by rw [← pow_add, hex]

end BinaryFieldCounterexamples
