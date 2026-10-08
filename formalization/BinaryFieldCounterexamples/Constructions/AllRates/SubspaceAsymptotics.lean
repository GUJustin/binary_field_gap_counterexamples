/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.SubspaceGaussianCount
public import BinaryFieldCounterexamples.Counting.GaussianSharpBound
public import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Tactic.FieldSimp

/-!
# The codimension-s population is Theta_s(N^s)

The opening paragraph of manuscript Section 4.2
(`sections/constructions/all-rates-certain-failure.tex:7`) states that a binary
domain of size `N` has `Theta_s(N^s)` subspaces of codimension `s`.
The exact count below concerns actual subspaces of the supplied domain, represented
by submodules of its carrier. Its explicit bounds have constants
`2^(-s*s)` and `4*2^(-s*s)`, independent of the domain and its dimension.
These hold throughout `d >= s`, hence throughout the paper's range `d >= 2s`.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- Section 4.2's `Theta_s(N^s)` subspace count: explicit positive constants
depending only on `s` bound the Gaussian coefficient when `N=2^d`.
The upper bound is strict and the bounds hold for every `s <= d`. -/
theorem gaussianBinomial_codimension_power_bounds (d s : ℕ) (hsd : s ≤ d) :
    ((2 : ℚ) ^ d) ^ s / (2 : ℚ) ^ (s * s) ≤ gaussianBinomial 2 d s ∧
      (gaussianBinomial 2 d s : ℚ) <
        4 * (((2 : ℚ) ^ d) ^ s / (2 : ℚ) ^ (s * s)) := by
  have hexp : d * s = s * (d - s) + s * s := by
    have := Nat.sub_add_cancel hsd
    nlinarith
  have hpower : ((2 : ℚ) ^ d) ^ s / (2 : ℚ) ^ (s * s) =
      (2 : ℚ) ^ (s * (d - s)) := by
    rw [← pow_mul, hexp, pow_add]
    field_simp
  rw [hpower]
  obtain ⟨hl, hu⟩ := gaussianBinomial_sharp_bounds 2 d s (by decide) hsd
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

/-- Section 4.2's exact codimension-`s` population and its `Theta_s(N^s)`
bounds, for the actual subspaces of a supplied binary additive domain `D`.
A submodule of `D` of dimension `d-s` is a codimension-`s` subspace of `D`;
the two comparison constants depend only on `s`, uniformly over `D` and `d`. -/
theorem binary_codimension_subspaces_count_and_bounds
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) (d s : ℕ) (hD : Nat.card D = 2 ^ d) (hsd : s ≤ d) :
    Nat.card (subspacesOfFinrank (ZMod 2) D (d - s)) = gaussianBinomial 2 d s ∧
      (Nat.card D : ℚ) ^ s / (2 : ℚ) ^ (s * s) ≤
        Nat.card (subspacesOfFinrank (ZMod 2) D (d - s)) ∧
      (Nat.card (subspacesOfFinrank (ZMod 2) D (d - s)) : ℚ) <
        4 * ((Nat.card D : ℚ) ^ s / (2 : ℚ) ^ (s * s)) := by
  have hdim : Module.finrank (ZMod 2) D = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD] at h
    simp only [Nat.card_eq_fintype_card, ZMod.card] at h
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h.symm
  have hcount : Nat.card (subspacesOfFinrank (ZMod 2) D (d - s)) =
      gaussianBinomial 2 d s := by
    rw [subspacesOfFinrank_card_eq_gaussianBinomial (d - s)
      (by rw [hdim]; exact Nat.sub_le _ _), ZMod.card, hdim]
    exact (gaussianBinomial_symm 2 d s (by decide) hsd).symm
  refine ⟨hcount, ?_⟩
  rw [hcount, hD]
  push_cast
  exact gaussianBinomial_codimension_power_bounds d s hsd

/-- The literal `Theta_s(N^s)` statement from the opening of Section 4.2,
for `N=2^d` as `d` grows with fixed `s`. The Gaussian coefficient has already
been identified with the actual subspace count by the preceding theorem. -/
theorem gaussianBinomial_codimension_isTheta (s : ℕ) :
    Asymptotics.IsTheta Filter.atTop
      (fun d : ℕ => (gaussianBinomial 2 d s : ℝ))
      (fun d : ℕ => ((2 : ℝ) ^ d) ^ s) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 4
    filter_upwards [Filter.eventually_ge_atTop s] with d hsd
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hu := (gaussianBinomial_sharp_bounds 2 d s (by decide) hsd).2
    have huR : (gaussianBinomial 2 d s : ℝ) < 4 * (2 : ℝ) ^ (s * (d - s)) := by
      exact_mod_cast hu
    have hexp : s * (d - s) ≤ d * s := by
      have := Nat.sub_le d s
      nlinarith
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hp' : (2 : ℝ) ^ (s * (d - s)) ≤ ((2 : ℝ) ^ d) ^ s := by
      simpa only [← pow_mul] using hp
    exact huR.le.trans (mul_le_mul_of_nonneg_left hp' (by norm_num))
  · apply Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ (s * s))
    filter_upwards [Filter.eventually_ge_atTop s] with d hsd
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hl := (gaussianBinomial_sharp_bounds 2 d s (by decide) hsd).1
    have hlR : (2 : ℝ) ^ (s * (d - s)) ≤ (gaussianBinomial 2 d s : ℝ) := by
      exact_mod_cast hl
    have hexp : d * s = s * s + s * (d - s) := by
      have := Nat.sub_add_cancel hsd
      nlinarith
    rw [← pow_mul, hexp, pow_add]
    exact mul_le_mul_of_nonneg_left hlR (by positivity)

/-- Section 4.2's `Theta_s(N^s)` claim for actual codimension-`s` subspaces
of the canonical binary domain `Fin d → ZMod 2`, whose size is `N=2^d`.
This is a statement about subspaces, not merely about the Gaussian formula. -/
theorem binary_codimension_subspaces_isTheta (s : ℕ) :
    Asymptotics.IsTheta Filter.atTop
      (fun d : ℕ =>
        (Nat.card (subspacesOfFinrank (ZMod 2) (Fin d → ZMod 2) (d - s)) : ℝ))
      (fun d : ℕ => ((2 : ℝ) ^ d) ^ s) := by
  have hcount : (fun d : ℕ =>
        (Nat.card (subspacesOfFinrank (ZMod 2) (Fin d → ZMod 2) (d - s)) : ℝ))
      =ᶠ[Filter.atTop] fun d : ℕ => (gaussianBinomial 2 d s : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop s] with d hsd
    have hdim : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by simp
    rw [subspacesOfFinrank_card_eq_gaussianBinomial (d - s)
      (by rw [hdim]; exact Nat.sub_le _ _), ZMod.card, hdim]
    exact_mod_cast (gaussianBinomial_symm 2 d s (by decide) hsd).symm
  exact hcount.trans_isTheta (gaussianBinomial_codimension_isTheta s)

end BinaryFieldCounterexamples
