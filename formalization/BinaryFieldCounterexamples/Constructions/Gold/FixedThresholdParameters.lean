/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
/-!
# Fixed parameters below half agreement
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- For a supplied extension exponent, a rank parameter can be chosen later to
clear any fixed agreement threshold below one half. -/
theorem exists_fixed_threshold_rank_of_exponent (a : ℝ) (e : ℕ) (ha : a<1/2) :
    ∃ t : ℕ, e≤t ∧ a<1/2-1/(2:ℝ)^(t+1) := by
  have hgap : 0<1/2-a := sub_pos.mpr ha
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (1/(1/2-a)) (by norm_num : (1:ℝ)<2)
  let t := max e m
  have het : e≤t := Nat.le_max_left _ _
  have hmt : m≤t+1 := (Nat.le_max_right e m).trans (Nat.le_succ _)
  have hp : (2:ℝ)^m≤(2:ℝ)^(t+1) := pow_le_pow_right₀ (by norm_num) hmt
  have hinv : 1/(1/2-a)<(2:ℝ)^(t+1) := hm.trans_le hp
  have hsmall : 1/(2:ℝ)^(t+1)<1/2-a := by
    have hh := one_div_lt_one_div_of_lt (by positivity : (0:ℝ)<1/(1/2-a)) hinv
    simpa [one_div_div] using hh
  exact ⟨t,het,by linarith⟩

/-- Below half agreement, one can choose a fixed extension exponent above the
proposed polynomial degree and then a fixed Gold rank parameter clearing the
agreement threshold. -/
theorem exists_fixed_threshold_parameters (a b : ℝ) (ha : a<1/2) :
    ∃ e t : ℕ, 2≤e ∧ (b+1)<e ∧ e≤t ∧
      a<1/2-1/(2:ℝ)^(t+1) := by
  obtain ⟨e,he⟩ := exists_nat_gt (max (b+1) 2 : ℝ)
  have he2 : 2≤e := by
    exact_mod_cast (lt_of_le_of_lt (le_max_right (b+1) 2) he).le
  have heb : b+1<(e:ℝ) := lt_of_le_of_lt (le_max_left (b+1) 2) he
  have hgap : 0<1/2-a := sub_pos.mpr ha
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/(1/2-a)) (by norm_num : (1:ℝ)<2)
  let t := max e n
  have het : e≤t := Nat.le_max_left _ _
  have hnt : n≤t+1 := (Nat.le_max_right e n).trans (Nat.le_succ _)
  have hp : (2:ℝ)^n≤(2:ℝ)^(t+1) := by
    exact pow_le_pow_right₀ (by norm_num) hnt
  have hinv : 1/(1/2-a)<(2:ℝ)^(t+1) := hn.trans_le hp
  have hsmall : 1/(2:ℝ)^(t+1)<1/2-a := by
    have hh := one_div_lt_one_div_of_lt (by positivity : (0:ℝ)<1/(1/2-a)) hinv
    simpa [one_div_div] using hh
  exact ⟨e,t,he2,heb,het,by linarith⟩

end BinaryFieldCounterexamples.Gold
