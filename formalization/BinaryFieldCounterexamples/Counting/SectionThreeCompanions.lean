/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.BalancedPadding
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneCount

/-! # Assembled set-level padding and small Gaussian counts from Section 3 -/

@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- Lemma 3.18: one exact-size padding set satisfies both the intersection and
union bounds simultaneously, with the paper's exact deviation. -/
theorem exists_balanced_fixedSize_padding_full
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (D : Finset α) (I : Finset ι) (A : ι → Finset α) (T w : ℕ)
    (hA : ∀ i ∈ I, A i ⊆ D ∧ (A i).card = T) (hwD : w ≤ D.card) :
    ∃ W : Finset α, W ⊆ D ∧ W.card = w ∧ ∀ i ∈ I,
      ((W ∩ A i).card : ℝ) ≤ (w : ℝ) * T / D.card +
        Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card)) ∧
      (w : ℝ) + (1 - (w : ℝ) / D.card) * T -
        Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card)) ≤ (W ∪ A i).card := by
  obtain ⟨W, hWD, hW, hbound⟩ := exists_balanced_fixedSize_padding D I A T w hA hwD
  refine ⟨W, hWD, hW, fun i hi ↦ ⟨hbound i hi, ?_⟩⟩
  have hc := Finset.card_union_add_card_inter W (A i)
  rw [hW, (hA i hi).2] at hc
  have hcr : ((W ∪ A i).card : ℝ) + (W ∩ A i).card = (w : ℝ) + T := by
    exact_mod_cast hc
  have hb := hbound i hi
  rw [show (w : ℝ) + (1 - (w : ℝ) / D.card) * T =
    (w : ℝ) + T - (w : ℝ)*T/D.card by ring]
  linarith

/-- The small-case Gaussian formula in Section 3: the binary one-dimensional
subspaces number `2^d - 1`, including the zero-dimensional ambient space. -/
theorem gaussianBinomial_binary_one (d : ℕ) : gaussianBinomial 2 d 1 = 2^d - 1 := by
  cases d with
  | zero => norm_num [gaussianBinomial]
  | succ d => norm_num [gaussianBinomial, Finset.prod_range_succ]

/-- The small-case Gaussian formula in Section 3: the binary two-dimensional
subspaces number `(2^d-1)(2^d-2)/6`, including ambient dimensions below two. -/
theorem gaussianBinomial_binary_two (d : ℕ) :
    gaussianBinomial 2 d 2 = (2^d-1)*(2^d-2)/6 := by
  by_cases hd : 2 ≤ d
  · norm_num [gaussianBinomial, hd, Finset.prod_range_succ]
  · have hdlt : d < 2 := by omega
    interval_cases d <;> norm_num [gaussianBinomial]

/-- The small-case Gaussian formula in Section 3: the binary three-dimensional
subspaces number `(2^d-1)(2^d-2)(2^d-4)/168`. -/
theorem gaussianBinomial_binary_three (d : ℕ) :
    gaussianBinomial 2 d 3 = (2^d-1)*(2^d-2)*(2^d-4)/168 := by
  by_cases hd : 3 ≤ d
  · norm_num [gaussianBinomial, hd, Finset.prod_range_succ]
  · have hdlt : d < 3 := by omega
    interval_cases d <;> norm_num [gaussianBinomial]

/-- Section 3's Gaussian dimension-removal formula, assembled in the literal
rational form from the Gaussian counting identity. -/
theorem gaussianBinomial_dimension_ratio (q n t : ℕ) (hq : 1 < q) (ht : t < n) :
    (((q : ℚ)^(n-t)-1)/((q : ℚ)^n-1)) * gaussianBinomial q n t =
      gaussianBinomial q (n-1) t := by
  have hc := gaussianPascal_dimension_ratio q n t hq ht.le
  rw [← gaussianBinomial_eq_gaussianPascal q n t hq,
    ← gaussianBinomial_eq_gaussianPascal q (n-1) t hq] at hc
  have hq1 : 1 ≤ q := by omega
  have hp1 : 1 ≤ q^(n-t) := Nat.one_le_pow _ _ hq1
  have hp2 : 1 ≤ q^n := Nat.one_le_pow _ _ hq1
  have hcr : (gaussianBinomial q n t : ℚ)*((q:ℚ)^(n-t)-1) =
      (gaussianBinomial q (n-1) t : ℚ)*((q:ℚ)^n-1) := by exact_mod_cast hc
  have hden : (q:ℚ)^n-1 ≠ 0 := by
    have hqQ : (1:ℚ) < q := by exact_mod_cast hq
    have hpow := one_lt_pow₀ hqQ (by omega : n ≠ 0)
    linarith
  apply (div_mul_eq_mul_div _ _ _).trans
  apply (div_eq_iff hden).2
  linarith

end BinaryFieldCounterexamples
