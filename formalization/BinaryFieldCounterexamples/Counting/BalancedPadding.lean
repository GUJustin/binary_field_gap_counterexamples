/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Exact-size balanced padding

A uniformly chosen subset of fixed size has hypergeometric intersection sizes.
Their factorial moments are bounded by the corresponding binomial moments, so
Hoeffding's lemma and a union bound produce one subset of the prescribed size
whose intersection with every set in a finite family is near its mean.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open Finset
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Factorial moments of intersection size under uniform fixed-size sampling. -/
theorem sum_choose_card_inter_powersetCard
    {α : Type*} [DecidableEq α] (D A : Finset α) (hAD : A ⊆ D)
    (w k : ℕ) (hkw : k ≤ w) :
    ∑ W ∈ D.powersetCard w, Nat.choose (W ∩ A).card k =
      Nat.choose A.card k * Nat.choose (D.card - k) (w - k) := by
  have hone (W : Finset α) (hWD : W ∈ D.powersetCard w) :
      Nat.choose (W ∩ A).card k =
        ∑ K ∈ A.powersetCard k, if K ⊆ W then 1 else 0 := by
    rw [← Finset.card_powersetCard]
    calc
      ((W ∩ A).powersetCard k).card =
          ((A.powersetCard k).filter fun K ↦ K ⊆ W).card := by
        congr 1
        ext K
        simp [Finset.mem_powersetCard, Finset.subset_inter_iff,
          and_assoc, and_comm]
      _ = ∑ K ∈ A.powersetCard k, if K ⊆ W then 1 else 0 := by
        induction (A.powersetCard k) using Finset.induction_on with
        | empty => simp
        | @insert K S hKS ih =>
            by_cases hKW : K ⊆ W <;> simp_all
  calc
    (∑ W ∈ D.powersetCard w, Nat.choose (W ∩ A).card k) =
        ∑ W ∈ D.powersetCard w,
          ∑ K ∈ A.powersetCard k, if K ⊆ W then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro W hWD
      rw [hone W hWD]
    _ = ∑ K ∈ A.powersetCard k,
        ∑ W ∈ D.powersetCard w, if K ⊆ W then 1 else 0 := by
      rw [Finset.sum_comm]
    _ =
    (∑ K ∈ A.powersetCard k,
          Nat.choose (D.card - k) (w - k)) := by
      apply Finset.sum_congr rfl
      intro K hKA
      have hKD : K ⊆ D := (Finset.mem_powersetCard.mp hKA).1.trans hAD
      have hKcard : K.card = k := (Finset.mem_powersetCard.mp hKA).2
      rw [← hKcard]
      rw [← Finset.card_filter_powersetCard_subset K D w hKD (by simpa [hKcard] using hkw)]
      induction (D.powersetCard w) using Finset.induction_on with
      | empty => simp
      | @insert U R hUR ih =>
          by_cases hKU : K ⊆ U <;> simp_all
    _ = Nat.choose A.card k * Nat.choose (D.card - k) (w - k) := by
      simp [Finset.card_powersetCard]

/-- Sampling without replacement has no larger normalized factorial moments
than sampling with replacement. -/
theorem descFactorial_ratio_le_pow_ratio
    (N T k : ℕ) (hTN : T ≤ N) (hkT : k ≤ T) (hN : 0 < N) :
    (T.descFactorial k : ℝ) / N.descFactorial k ≤
      ((T : ℝ) / N) ^ k := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← Finset.prod_div_distrib]
  have hp : (∏ i ∈ Finset.range k,
      ((T - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)) ≤
      ∏ _i ∈ Finset.range k, (T : ℝ) / N := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hiT : i ≤ T := by omega
    have hiN : i < N := lt_of_lt_of_le hik (hkT.trans hTN)
    rw [Nat.cast_sub hiT, Nat.cast_sub (le_of_lt hiN)]
    have hiNr : (i : ℝ) < N := by exact_mod_cast hiN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    apply (div_le_div_iff₀ (sub_pos.mpr hiNr) hNr).2
    have hTNr : (T : ℝ) ≤ N := by exact_mod_cast hTN
    have hir : (0 : ℝ) ≤ i := by positivity
    nlinarith
  simpa only [Finset.prod_const, Finset.card_range] using hp

/-- The normalized binomial coefficient ratio is bounded by the corresponding
with-replacement probability. -/
theorem choose_ratio_le_pow_ratio
    (N T k : ℕ) (hTN : T ≤ N) (hkT : k ≤ T) (hN : 0 < N) :
    (Nat.choose T k : ℝ) / Nat.choose N k ≤ ((T : ℝ) / N) ^ k := by
  have hkN : k ≤ N := hkT.trans hTN
  have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkN).ne'
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  calc
    (Nat.choose T k : ℝ) / Nat.choose N k =
        (T.descFactorial k : ℝ) / N.descFactorial k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      field_simp
    _ ≤ ((T : ℝ) / N) ^ k :=
      descFactorial_ratio_le_pow_ratio N T k hTN hkT hN

/-- Every coefficient in the fixed-size intersection MGF is bounded by the
corresponding binomial coefficient. -/
theorem hypergeometric_coefficient_le
    (N T w k : ℕ) (hTN : T ≤ N) (hwN : w ≤ N) (hkw : k ≤ w)
    (hN : 0 < N) :
    ((Nat.choose T k * Nat.choose (N - k) (w - k) : ℕ) : ℝ) /
        Nat.choose N w ≤
      Nat.choose w k * ((T : ℝ) / N) ^ k := by
  by_cases hkT : k ≤ T
  · have hkN : k ≤ N := hkw.trans hwN
    have hNw : (Nat.choose N w : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hwN).ne'
    have hNk : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hkN).ne'
    have hid := Nat.choose_mul (n := N) (k := w) (s := k) hkw
    have heq :
        ((Nat.choose T k * Nat.choose (N - k) (w - k) : ℕ) : ℝ) /
            Nat.choose N w =
          Nat.choose w k * ((Nat.choose T k : ℝ) / Nat.choose N k) := by
      push_cast
      field_simp
      have hmul := congrArg (Nat.choose T k * ·) hid.symm
      exact_mod_cast (show Nat.choose T k * Nat.choose (N - k) (w - k) *
          Nat.choose N k = Nat.choose T k * Nat.choose N w * Nat.choose w k by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
    rw [heq]
    gcongr
    exact choose_ratio_le_pow_ratio N T k hTN hkT hN
  · have hz : Nat.choose T k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hz, Nat.cast_zero, zero_mul, zero_div]
    positivity

/-- Exact generating-function expansion for fixed-size intersections. -/
theorem sum_one_add_pow_card_inter_powersetCard
    {α : Type*} [DecidableEq α] (D A : Finset α) (hAD : A ⊆ D)
    (w : ℕ) (_hwD : w ≤ D.card) (u : ℝ) :
    ∑ W ∈ D.powersetCard w, (1 + u) ^ (W ∩ A).card =
      ∑ k ∈ Finset.range (w + 1),
        (Nat.choose A.card k * Nat.choose (D.card - k) (w - k) : ℕ) * u ^ k := by
  have hbin (W : Finset α) (hWD : W ∈ D.powersetCard w) :
      (1 + u) ^ (W ∩ A).card =
        ∑ k ∈ Finset.range (w + 1), (Nat.choose (W ∩ A).card k : ℝ) * u ^ k := by
    have hcardW : W.card = w := (Finset.mem_powersetCard.mp hWD).2
    have hinter : (W ∩ A).card ≤ w := by
      rw [← hcardW]
      exact Finset.card_le_card Finset.inter_subset_left
    calc
      (1 + u) ^ (W ∩ A).card = (u + 1) ^ (W ∩ A).card := by rw [add_comm]
      _ = ∑ k ∈ Finset.range ((W ∩ A).card + 1),
          (Nat.choose (W ∩ A).card k : ℝ) * u ^ k := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro k _
        simp [mul_comm]
      _ = ∑ k ∈ Finset.range (w + 1),
          (Nat.choose (W ∩ A).card k : ℝ) * u ^ k := by
        rw [Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hinter 1))]
        intro k hkw hk
        have hkgt : (W ∩ A).card < k := by
          have := Finset.mem_range.mp hkw
          simp only [Finset.mem_range] at hk
          omega
        rw [Nat.choose_eq_zero_of_lt hkgt]
        simp
  calc
    (∑ W ∈ D.powersetCard w, (1 + u) ^ (W ∩ A).card) =
        ∑ W ∈ D.powersetCard w, ∑ k ∈ Finset.range (w + 1),
          (Nat.choose (W ∩ A).card k : ℝ) * u ^ k := by
      apply Finset.sum_congr rfl
      intro W hWD
      rw [hbin W hWD]
    _ = ∑ k ∈ Finset.range (w + 1), ∑ W ∈ D.powersetCard w,
          (Nat.choose (W ∩ A).card k : ℝ) * u ^ k := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (w + 1),
        (Nat.choose A.card k * Nat.choose (D.card - k) (w - k) : ℕ) * u ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkw : k ≤ w := by have := Finset.mem_range.mp hk; omega
      rw [← Finset.sum_mul]
      have hsum := sum_choose_card_inter_powersetCard D A hAD w k hkw
      have hsumr : (∑ W ∈ D.powersetCard w,
          (Nat.choose (W ∩ A).card k : ℝ)) =
          ((Nat.choose A.card k * Nat.choose (D.card - k) (w - k) : ℕ) : ℝ) := by
        exact_mod_cast hsum
      rw [hsumr]

/-- The fixed-size intersection MGF is bounded by the with-replacement
binomial MGF. -/
theorem fixedSize_intersection_mgf_le_binomial
    {α : Type*} [DecidableEq α] (D A : Finset α) (hAD : A ⊆ D)
    (w : ℕ) (hwD : w ≤ D.card) (u : ℝ) (hu : 0 ≤ u) :
    (∑ W ∈ D.powersetCard w, (1 + u) ^ (W ∩ A).card) /
        Nat.choose D.card w ≤
      (1 + (A.card : ℝ) / D.card * u) ^ w := by
  by_cases hD0 : D.card = 0
  · have hw0 : w = 0 := by omega
    subst w
    simp
  have hDpos : 0 < D.card := Nat.pos_of_ne_zero hD0
  rw [sum_one_add_pow_card_inter_powersetCard D A hAD w hwD u]
  rw [Finset.sum_div]
  calc
    (∑ k ∈ Finset.range (w + 1),
        ((Nat.choose A.card k * Nat.choose (D.card - k) (w - k) : ℕ) : ℝ) *
            u ^ k / Nat.choose D.card w) ≤
        ∑ k ∈ Finset.range (w + 1),
          (Nat.choose w k : ℝ) * ((A.card : ℝ) / D.card) ^ k * u ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkw : k ≤ w := by have := Finset.mem_range.mp hk; omega
      have hc := hypergeometric_coefficient_le D.card A.card w k
        (Finset.card_le_card hAD) hwD hkw hDpos
      calc
        ((Nat.choose A.card k * Nat.choose (D.card - k) (w - k) : ℕ) : ℝ) *
              u ^ k / Nat.choose D.card w =
            (((Nat.choose A.card k * Nat.choose (D.card - k) (w - k) : ℕ) : ℝ) /
              Nat.choose D.card w) * u ^ k := by ring
        _ ≤ ((Nat.choose w k : ℝ) * ((A.card : ℝ) / D.card) ^ k) * u ^ k := by
          exact mul_le_mul_of_nonneg_right hc (pow_nonneg hu _)
        _ = (Nat.choose w k : ℝ) * ((A.card : ℝ) / D.card) ^ k * u ^ k := rfl
    _ = (1 + (A.card : ℝ) / D.card * u) ^ w := by
      rw [show 1 + (A.card : ℝ) / D.card * u =
        (A.card : ℝ) / D.card * u + 1 by ring]
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      simp
      ring

/-- Hoeffding's lemma specialized to one Bernoulli variable, in the scalar
form used after the hypergeometric comparison. -/
theorem bernoulli_centered_mgf_le (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.exp (-t * p) * (1 - p + p * Real.exp t) ≤ Real.exp (t ^ 2 / 8) := by
  let q : Set.Icc (0 : ℝ) 1 := ⟨p, hp0, hp1⟩
  let μ : Measure ℝ := ProbabilityTheory.bernoulliMeasure 1 0 q
  let X : ℝ → ℝ := fun x ↦ x - p
  have hmean : ∫ x, X x ∂μ = 0 := by
    simp only [μ, X]
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    simp [q]
    ring
  have hbound : ∀ᵐ x ∂μ, X x ∈ Set.Icc (-p) (1 - p) := by
    rw [MeasureTheory.ae_iff]
    simp only [μ, X, ProbabilityTheory.bernoulliMeasure_def]
    simp
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := X) (a := -p) (b := 1 - p) (by fun_prop) hbound hmean
  have hmgf := hsub.mgf_le t
  simp only [ProbabilityTheory.mgf, μ, X] at hmgf
  rw [ProbabilityTheory.integral_bernoulliMeasure] at hmgf
  have hnorm : ‖(1 - p) - (-p)‖₊ = 1 := by
    norm_num
  rw [hnorm] at hmgf
  norm_num only [q, NNReal.coe_one, one_div] at hmgf
  have hpos : Real.exp (t * (1 - p)) = Real.exp (-t * p) * Real.exp t := by
    rw [show t * (1 - p) = -t * p + t by ring, Real.exp_add]
  have hzero : Real.exp (t * (0 - p)) = Real.exp (-t * p) := by
    congr 1
    ring
  rw [hpos, hzero] at hmgf
  norm_num at hmgf
  simp only [div_eq_mul_inv] at hmgf ⊢
  convert hmgf using 1 <;> ring

/-- Centered MGF bound for a fixed-size intersection. -/
theorem fixedSize_centered_intersection_mgf_le
    {α : Type*} [DecidableEq α] (D A : Finset α) (hAD : A ⊆ D)
    (w : ℕ) (hwD : w ≤ D.card) (t : ℝ) (ht : 0 ≤ t) :
    (∑ W ∈ D.powersetCard w,
        Real.exp (t * ((W ∩ A).card - (w : ℝ) * A.card / D.card))) /
        Nat.choose D.card w ≤ Real.exp ((w : ℝ) * t ^ 2 / 8) := by
  by_cases hD0 : D.card = 0
  · have hw0 : w = 0 := by omega
    subst w
    simp
  have hDpos : 0 < D.card := Nat.pos_of_ne_zero hD0
  let p : ℝ := (A.card : ℝ) / D.card
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hDpos)).2
    exact_mod_cast Finset.card_le_card hAD
  let u : ℝ := Real.exp t - 1
  have hu : 0 ≤ u := by
    dsimp [u]
    exact sub_nonneg.mpr (Real.one_le_exp ht)
  have hraw := fixedSize_intersection_mgf_le_binomial D A hAD w hwD u hu
  have hone : 1 + u = Real.exp t := by simp [u]
  have hsum :
      (∑ W ∈ D.powersetCard w,
          Real.exp (t * ((W ∩ A).card - (w : ℝ) * p))) /
          Nat.choose D.card w =
        Real.exp (-t * (w : ℝ) * p) *
          ((∑ W ∈ D.powersetCard w, (1 + u) ^ (W ∩ A).card) /
            Nat.choose D.card w) := by
    have hsumraw : (∑ W ∈ D.powersetCard w,
        Real.exp (t * ((W ∩ A).card - (w : ℝ) * p))) =
        Real.exp (-t * (w : ℝ) * p) *
          ∑ W ∈ D.powersetCard w, (1 + u) ^ (W ∩ A).card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W hW
      rw [hone, ← Real.exp_nat_mul]
      rw [← Real.exp_add]
      congr 1
      ring

    have hc : (Nat.choose D.card w : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hwD).ne'
    rw [hsumraw]
    field_simp
  have hpform : (w : ℝ) * A.card / D.card = (w : ℝ) * p := by
    dsimp [p]
    ring
  rw [hpform]
  change (∑ W ∈ D.powersetCard w,
      Real.exp (t * ((W ∩ A).card - (w : ℝ) * p))) /
      Nat.choose D.card w ≤ _
  rw [hsum]
  calc
    Real.exp (-t * (w : ℝ) * p) *
          ((∑ W ∈ D.powersetCard w, (1 + u) ^ (W ∩ A).card) /
            Nat.choose D.card w) ≤
        Real.exp (-t * (w : ℝ) * p) * (1 + p * u) ^ w := by
      gcongr
    _ = (Real.exp (-t * p) * (1 - p + p * Real.exp t)) ^ w := by
      rw [mul_pow]
      rw [show Real.exp (-t * (w : ℝ) * p) = Real.exp (-t * p) ^ w by
        rw [← Real.exp_nat_mul]
        congr 1
        ring]
      congr 2
      simp [u]
      ring
    _ ≤ (Real.exp (t ^ 2 / 8)) ^ w := by
      exact pow_le_pow_left₀ (by positivity) (bernoulli_centered_mgf_le p t hp0 hp1) _
    _ = Real.exp ((w : ℝ) * t ^ 2 / 8) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Hypergeometric Hoeffding upper-tail bound, expressed as the fraction of
bad fixed-size subsets. -/
theorem fixedSize_intersection_upperTail
    {α : Type*} [DecidableEq α] (D A : Finset α) (hAD : A ⊆ D)
    (w : ℕ) (hw0 : 0 < w) (hwD : w ≤ D.card) (a : ℝ) (ha : 0 ≤ a) :
    (((D.powersetCard w).filter fun W ↦
        (w : ℝ) * A.card / D.card + a < (W ∩ A).card).card : ℝ) /
        Nat.choose D.card w ≤ Real.exp (-2 * a ^ 2 / w) := by
  have hDpos : 0 < D.card := lt_of_lt_of_le hw0 hwD
  let p : ℝ := (A.card : ℝ) / D.card
  let t : ℝ := 4 * a / w
  have ht : 0 ≤ t := by positivity
  let bad := (D.powersetCard w).filter fun W ↦
    (w : ℝ) * p + a < (W ∩ A).card
  let Z : Finset α → ℝ := fun W ↦
    Real.exp (t * ((W ∩ A).card - (w : ℝ) * p))
  have hbadsub : bad ⊆ D.powersetCard w := Finset.filter_subset _ _
  have hlower : (bad.card : ℝ) * Real.exp (t * a) ≤
      ∑ W ∈ D.powersetCard w, Z W := by
    calc
      (bad.card : ℝ) * Real.exp (t * a) =
          ∑ W ∈ bad, Real.exp (t * a) := by simp
      _ ≤ ∑ W ∈ bad, Z W := by
        apply Finset.sum_le_sum
        intro W hW
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ ht
        have hmem := (Finset.mem_filter.mp hW).2
        linarith
      _ ≤ ∑ W ∈ D.powersetCard w, Z W := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hbadsub (fun _ _ _ ↦ Real.exp_pos _ |>.le)
  have hmgf := fixedSize_centered_intersection_mgf_le D A hAD w hwD t ht
  have hchoose : (0 : ℝ) < Nat.choose D.card w := by
    exact_mod_cast Nat.choose_pos hwD
  have hsum : (∑ W ∈ D.powersetCard w, Z W) ≤
      Nat.choose D.card w * Real.exp ((w : ℝ) * t ^ 2 / 8) := by
    have hh := (div_le_iff₀ hchoose).mp hmgf
    simpa only [Z, p, mul_div_assoc, mul_comm] using hh
  have hfrac : (bad.card : ℝ) / Nat.choose D.card w ≤
      Real.exp ((w : ℝ) * t ^ 2 / 8 - t * a) := by
    have hexp : 0 < Real.exp (t * a) := Real.exp_pos _
    rw [Real.exp_sub]
    apply (div_le_div_iff₀ hchoose hexp).2
    calc
      (bad.card : ℝ) * Real.exp (t * a) ≤
          ∑ W ∈ D.powersetCard w, Z W := hlower
      _ ≤ Real.exp ((w : ℝ) * t ^ 2 / 8) * Nat.choose D.card w := by
        simpa only [mul_comm] using hsum
  have hexponent : (w : ℝ) * t ^ 2 / 8 - t * a = -2 * a ^ 2 / w := by
    dsimp [t]
    field_simp
    ring
  rw [hexponent] at hfrac
  dsimp only [bad, p] at hfrac
  convert hfrac using 1 <;> ring


/-- A union indexed by a finite set has cardinality at most the sum of the
cardinalities of its members. -/
theorem card_biUnion_le_sum_card
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) :
    (I.biUnion S).card ≤ ∑ i ∈ I, (S i).card := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert]
      calc
        (S i ∪ I.biUnion S).card ≤ (S i).card + (I.biUnion S).card :=
          Finset.card_union_le (S i) (I.biUnion S)
        _ ≤ (S i).card + ∑ j ∈ I, (S j).card := Nat.add_le_add_left ih _
        _ = ∑ j ∈ insert i I, (S j).card := by simp [hi]

/-- Exact-size balanced padding: among all subsets of a prescribed size, one
simultaneously has near-average intersection with every member of a finite
family. -/
theorem exists_balanced_fixedSize_padding
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (D : Finset α) (I : Finset ι) (A : ι → Finset α)
    (T w : ℕ)
    (hA : ∀ i ∈ I, A i ⊆ D ∧ (A i).card = T)
    (hwD : w ≤ D.card) :
    ∃ W : Finset α, W ⊆ D ∧ W.card = w ∧ ∀ i ∈ I,
      ((W ∩ A i).card : ℝ) ≤
        (w : ℝ) * T / D.card +
          Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card)) := by
  by_cases hI : I.Nonempty
  · by_cases hw0 : w = 0
    · refine ⟨∅, Finset.empty_subset _, by simp [hw0], ?_⟩
      intro i hi
      have hIcard : 1 ≤ I.card := Finset.one_le_card.mpr hI
      have hlog : 0 ≤ Real.log (2 * (I.card : ℝ)) := by
        apply Real.log_nonneg
        have hone : 1 ≤ 2 * I.card := by omega
        exact_mod_cast hone
      have hsqrt : 0 ≤ Real.sqrt (((0 : ℝ) / 2) * Real.log (2 * I.card)) :=
        Real.sqrt_nonneg _
      simpa [hw0] using hsqrt
    · have hwpos : 0 < w := Nat.pos_of_ne_zero hw0
      have hDpos : 0 < D.card := lt_of_lt_of_le hwpos hwD
      have hIcard : 0 < I.card := Finset.card_pos.mpr hI
      let a : ℝ := Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card))
      let bad : ι → Finset (Finset α) := fun i ↦
        (D.powersetCard w).filter fun W ↦
          (w : ℝ) * T / D.card + a < (W ∩ A i).card
      let U : Finset (Finset α) := I.biUnion bad
      let C : ℕ := Nat.choose D.card w
      have hqpos : (0 : ℝ) < 2 * I.card := by positivity
      have hlog : 0 ≤ Real.log (2 * (I.card : ℝ)) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ I.card := by exact_mod_cast hIcard
        linarith
      have hins : 0 ≤ ((w : ℝ) / 2) * Real.log (2 * I.card) :=
        mul_nonneg (by positivity) hlog
      have ha : 0 ≤ a := Real.sqrt_nonneg _
      have ha2 : a ^ 2 = ((w : ℝ) / 2) * Real.log (2 * I.card) := by
        dsimp [a]
        exact Real.sq_sqrt hins
      have hexp : Real.exp (-2 * a ^ 2 / w) = 1 / (2 * I.card : ℝ) := by
        rw [ha2]
        have hwR : (w : ℝ) ≠ 0 := by positivity
        rw [show -2 * (((w : ℝ) / 2) * Real.log (2 * I.card)) / w =
            -Real.log (2 * I.card) by field_simp]
        rw [Real.exp_neg, Real.exp_log hqpos]
        simp [div_eq_mul_inv]
      have hbad (i : ι) (hi : i ∈ I) :
          ((bad i).card : ℝ) / C ≤ 1 / (2 * I.card : ℝ) := by
        have ht := fixedSize_intersection_upperTail D (A i) (hA i hi).1
          w hwpos hwD a ha
        rw [(hA i hi).2, hexp] at ht
        exact ht
      have hCpos : (0 : ℝ) < C := by
        dsimp [C]
        exact_mod_cast Nat.choose_pos hwD
      have hbad' (i : ι) (hi : i ∈ I) :
          ((bad i).card : ℝ) ≤ C / (2 * I.card : ℝ) := by
        have := (div_le_iff₀ hCpos).mp (hbad i hi)
        calc
          ((bad i).card : ℝ) ≤ 1 / (2 * I.card : ℝ) * C := this
          _ = C / (2 * I.card : ℝ) := by ring
      have hUreal : (U.card : ℝ) ≤ (C : ℝ) / 2 := by
        have hUcard : U.card ≤ ∑ i ∈ I, (bad i).card := by
          exact card_biUnion_le_sum_card I bad
        calc
          (U.card : ℝ) ≤ ∑ i ∈ I, ((bad i).card : ℝ) := by exact_mod_cast hUcard
          _ ≤ ∑ _i ∈ I, (C : ℝ) / (2 * I.card : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hbad' i hi
          _ = (C : ℝ) / 2 := by
            rw [Finset.sum_const, Finset.card_eq_sum_ones]
            simp only [nsmul_eq_mul]
            have hIcR : (I.card : ℝ) ≠ 0 := by positivity
            field_simp
      have hUlt : U.card < C := by
        have hhalf : (C : ℝ) / 2 < C := by linarith
        exact_mod_cast lt_of_le_of_lt hUreal hhalf
      have hUlt' : U.card < (D.powersetCard w).card := by
        simpa [C, Finset.card_powersetCard] using hUlt
      obtain ⟨W, hWp, hWU⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hUlt'
      refine ⟨W, (Finset.mem_powersetCard.mp hWp).1,
        (Finset.mem_powersetCard.mp hWp).2, ?_⟩
      intro i hi
      have hWbad : W ∉ bad i := by
        intro hmem
        apply hWU
        exact Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩
      have hnotlt : ¬ ((w : ℝ) * T / D.card + a < (W ∩ A i).card) := by
        intro hlt
        apply hWbad
        exact Finset.mem_filter.mpr ⟨hWp, hlt⟩
      simpa only [a] using le_of_not_gt hnotlt
  · obtain ⟨W, hW⟩ := Finset.powersetCard_nonempty.mpr hwD
    refine ⟨W, (Finset.mem_powersetCard.mp hW).1,
      (Finset.mem_powersetCard.mp hW).2, ?_⟩
    intro i hi
    exact (hI ⟨i, hi⟩).elim

end BinaryFieldCounterexamples
