/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FullFieldExtensionParameters
public import BinaryFieldCounterexamples.Counting.GaussianSharpBound
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Corollary 5.3: the full-field fixed-extension logarithmic expansion

The proof of Corollary 5.3, p. 38, prints
`log₂(L/N^e) = n - 2e² + 3e - 1 + O_e(1)` for the full-field Gold
population. Here `N = 2^(2n)` and `L` is the guaranteed locator count from
Theorem 5.1, as identified by `Gold.full_field_extension_list_eq`.
For every `e ≥ 2` and `n ≥ e + 2`, its logarithm differs from the printed
polynomial by at most two. This universal constant in particular supplies
an explicit constant depending only on `e` for the printed error term.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

/-- Corollary 5.3's Gaussian product calculation, with a uniform two-unit
upper error for the logarithm of the paper's integral Gaussian coefficient. -/
theorem fixed_extension_gaussian_log_bounds (n e : ℕ) (he : 2 ≤ e)
    (hn : e + 2 ≤ n) :
    (2 * ((e-1)*(n-e+1) : ℕ) : ℝ) ≤
      Real.logb 2 (gaussianBinomial 4 n (e-1) : ℝ) ∧
    Real.logb 2 (gaussianBinomial 4 n (e-1) : ℝ) ≤
      (2 * ((e-1)*(n-e+1) : ℕ) : ℝ) + 2 := by
  have hg := gaussianBinomial_sharp_bounds 4 n (e-1) (by decide) (by omega)
  rw [show n-(e-1)=n-e+1 by omega] at hg
  have hlo : (2:ℝ)^(2*((e-1)*(n-e+1))) ≤
      (gaussianBinomial 4 n (e-1):ℝ) := by
    have hh : (4:ℝ)^((e-1)*(n-e+1)) ≤
        (gaussianBinomial 4 n (e-1):ℝ) := by exact_mod_cast hg.1
    simpa only [show (4:ℝ)=2^2 by norm_num, ←pow_mul] using hh
  have hhi : (gaussianBinomial 4 n (e-1):ℝ) ≤
      (2:ℝ)^(2*((e-1)*(n-e+1))+2) := by
    have hh : (gaussianBinomial 4 n (e-1):ℝ) <
        4*(4:ℝ)^((e-1)*(n-e+1)) := by exact_mod_cast hg.2
    have hp : (4:ℝ)*(4:ℝ)^((e-1)*(n-e+1)) =
        (2:ℝ)^(2*((e-1)*(n-e+1))+2) := by
      rw [show (4:ℝ)=2^2 by norm_num, ←pow_mul, pow_add]
      ring
    exact hp ▸ hh.le
  have hgp : 0 < (gaussianBinomial 4 n (e-1):ℝ) :=
    lt_of_lt_of_le (by positivity) hlo
  have hloglo := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : (0:ℝ)<2^(2*((e-1)*(n-e+1)))) hlo
  have hloghi := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hgp hhi
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hloglo hloghi
  constructor
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hloglo
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hloghi

/-- Corollary 5.3's printed full-field logarithmic expansion for its guaranteed
Gold locator population `L`. The interval is valid already at `n ≥ e+2`;
its error constants minus one and plus two are independent of both parameters. -/
theorem gold_full_field_fixed_extension_log_expansion (n e : ℕ)
    (he : 2 ≤ e) (hn : e + 2 ≤ n) :
    let N : ℕ := 2^(2*n)
    let L : ℕ := 2^(2*(n-e+1))*(2^(n+e-1)-1)*gaussianBinomial 4 n (e-1)
    let E : ℝ := (n:ℝ)-2*(e:ℝ)^2+3*(e:ℝ)-1
    E-1 ≤ Real.logb 2 ((L:ℝ)/(N:ℝ)^e) ∧
      Real.logb 2 ((L:ℝ)/(N:ℝ)^e) ≤ E+2 := by
  dsimp only
  have hs : (2:ℕ)^(n+e-2) ≤ 2^(n+e-1)-1 := by
    have hp : (2:ℕ)^(n+e-1) = 2^(n+e-2)*2 := by
      rw [show n+e-1=(n+e-2)+1 by omega,pow_succ]
    rw [hp]
    have : 0 < (2:ℕ)^(n+e-2) := by positivity
    omega
  have hsp : 0 < (2^(n+e-1)-1:ℕ) :=
    lt_of_lt_of_le (by positivity) hs
  have hslo : (2:ℝ)^(n+e-2) ≤ ((2^(n+e-1)-1:ℕ):ℝ) := by
    exact_mod_cast hs
  have hshi : ((2^(n+e-1)-1:ℕ):ℝ) ≤ (2:ℝ)^(n+e-1) := by
    exact_mod_cast (Nat.sub_le ((2:ℕ)^(n+e-1)) 1)
  have hsR : 0 < ((2^(n+e-1)-1:ℕ):ℝ) := by exact_mod_cast hsp
  have hloglo := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : (0:ℝ)<2^(n+e-2)) hslo
  have hloghi := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hsR hshi
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    mul_one] at hloglo hloghi
  obtain ⟨hglo,hghi⟩ := fixed_extension_gaussian_log_bounds n e he hn
  have hgR : 0 < (gaussianBinomial 4 n (e-1):ℝ) := by
    have hg := pow_mul_sub_le_gaussianBinomial 4 n (e-1) (by decide) (by omega)
    exact_mod_cast (lt_of_lt_of_le (by positivity) hg)

  -- Separate the three actual population factors and the extension-field size.
  push_cast
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (ne_of_gt hgR),
    Real.logb_mul (by positivity) (ne_of_gt hsR),
    Real.logb_pow, Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
  have he1 : ((e-1:ℕ):ℝ) = (e:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤e)]
    norm_num
  have hne : ((n-e+1:ℕ):ℝ) = (n:ℝ)-(e:ℝ)+1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega : e≤n)]
    norm_num
  have hne1 : ((n+e-1:ℕ):ℝ) = (n:ℝ)+(e:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤n+e),Nat.cast_add]
    norm_num
  have hne2 : ((n+e-2:ℕ):ℝ) = (n:ℝ)+(e:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤n+e),Nat.cast_add]
    norm_num
  simp only [Nat.cast_mul,Nat.cast_ofNat,he1,hne] at hglo hghi ⊢
  rw [hne1] at hloghi
  rw [hne2] at hloglo
  constructor <;> nlinarith

/-- Corollary 5.3's `O_e(1)` term with the explicit constant `C(e)=2` for
all `e ≥ 2`, uniformly over every `n ≥ e+2`. -/
theorem gold_full_field_fixed_extension_log_error (n e : ℕ)
    (he : 2 ≤ e) (hn : e + 2 ≤ n) :
    let N : ℕ := 2^(2*n)
    let L : ℕ := 2^(2*(n-e+1))*(2^(n+e-1)-1)*gaussianBinomial 4 n (e-1)
    |Real.logb 2 ((L:ℝ)/(N:ℝ)^e)-((n:ℝ)-2*(e:ℝ)^2+3*(e:ℝ)-1)| ≤ 2 := by
  have h := gold_full_field_fixed_extension_log_expansion n e he hn
  dsimp only at h ⊢
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]
end BinaryFieldCounterexamples
