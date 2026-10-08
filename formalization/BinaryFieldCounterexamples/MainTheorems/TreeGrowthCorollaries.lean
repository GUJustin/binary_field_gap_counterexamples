/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.HalfRateDecisionTrees
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Main theorem companions: the tree growth remarks

The consequences after Corollary 6.7 and Theorem 6.10 retain one fixed pair
and its common and individual agreement guarantees. Height two gives a cubic
count at rate `3/8` over fields of size at least `N^4`, and the avoiding-tree
variant gives a linear-versus-field-size minimum at agreement `5/8`.
The quantified finite growth statement expresses the superquadratic claim:
any prescribed multiple of `N^2` is attained once the dimension is large
and `q/N^3` exceeds a constant depending on that multiple.
-/

@[expose] public section
namespace BinaryFieldCounterexamples

theorem count_of_probability_min (N q Z : ℕ) (c : ℝ) (e : ℕ)
    (hq : 0 < q)
    (hp : c * min ((N : ℝ)^e/q) (1/N) ≤ (Z : ℝ)/q) :
    c * min ((N : ℝ)^e) ((q : ℝ)/N) ≤ Z := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : (1 : ℝ)/N = ((q : ℝ)/N)/q := by field_simp
  rw [he, min_div_div_right hqR.le, ← mul_div_assoc] at hp
  exact (div_le_div_iff_of_pos_right hqR).mp hp

theorem eight_dvd_binary_size (d : ℕ) (hd : 3 ≤ d) : 8 ∣ 2 ^ d := by
  simpa using (pow_dvd_pow (2 : ℕ) hd)

/-- Corollary 6.7's height-two remark: at rate `3/8` and agreement `1/2`,
one pair has a cubic nonzero exceptional count whenever `q≥N^4`, uniformly
on every sufficiently large prescribed binary additive domain. -/
theorem half_agreement_trees_height_two_cubic :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → (2 ^ d) ^ 4 ≤ Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let K : ℕ := 3 * N / 8
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (N / 2 - 1) ∧
          c * (N : ℝ)^3 ≤ (nonzeroBadChallenges A K f g (N / 2)).card := by
  obtain ⟨c,hc,d₀,hbound⟩ := half_agreement_trees_asymptotic 2 (by decide)
  refine ⟨c,hc,max d₀ 3,?_⟩
  intro d hd F _ _ _ D hD hq4
  have hd3 : 3 ≤ d := (le_max_right _ _).trans hd
  have hN : 0 < 2 ^ d := by positivity
  have hN1 : 1 < 2 ^ d := one_lt_pow₀ (by decide) (by omega)
  have hq : 2 ^ d < Fintype.card F := by
    have hx : 2 ^ d < (2 ^ d)^4 := by
      simpa using (pow_lt_pow_right₀ hN1 (by decide : 1 < 4))
    exact hx.trans_le hq4
  have hK : 2 ^ d / 2 - 2 ^ d / 8 = 3 * 2 ^ d / 8 := by
    obtain ⟨m,hm⟩ := eight_dvd_binary_size d hd3
    omega
  have hb := hbound d ((le_max_left _ _).trans hd) (by simpa using hd3) F D hD hq
  dsimp only at hb
  norm_num only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub] at hb
  rw [hK] at hb
  obtain ⟨f,g,hcommon,hg,hf,hbad⟩ := hb
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hqR : ((2 ^ d : ℕ) : ℝ)^4 ≤ Fintype.card F := by exact_mod_cast hq4
  have hNR : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hmin : min (((2 ^ d : ℕ) : ℝ)^3) ((Fintype.card F : ℝ)/(2 ^ d : ℕ)) =
      ((2 ^ d : ℕ) : ℝ)^3 := min_eq_left ((le_div_iff₀ hNR).mpr (by nlinarith [hqR]))
  rwa [hmin] at hbad

/-- The height-two remark following Theorem 6.10: at rate `1/2` and
agreement `5/8`, every sufficiently large prescribed domain admits one pair
with `Ω(min{N,q/N})` nonzero challenges and the paper's individual bounds. -/
theorem half_rate_decision_trees_height_two_count :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → 2 ^ d < Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let K : ℕ := N / 2
        let T : ℕ := 5 * N / 8
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (T - 1) ∧
          c * min (N : ℝ) ((Fintype.card F : ℝ)/N) ≤
            (nonzeroBadChallenges A K f g T).card ∧
          c * min ((N : ℝ)/(Fintype.card F)) (1/N) ≤
            ((nonzeroBadChallenges A K f g T).card : ℝ)/(Fintype.card F) := by
  obtain ⟨c,hc,d₀,hbound⟩ := half_rate_decision_trees_probability 2 (by decide)
  refine ⟨c,hc,max d₀ 3,?_⟩
  intro d hd F _ _ _ D hD hq
  have hd3 : 3 ≤ d := (le_max_right _ _).trans hd
  have hT : 2 ^ d / 2 + 2 ^ d / 8 = 5 * 2 ^ d / 8 := by
    obtain ⟨m,hm⟩ := eight_dvd_binary_size d hd3
    omega
  have hb := hbound d ((le_max_left _ _).trans hd) (by simpa using hd3) F D hD hq
  dsimp only at hb
  norm_num only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, pow_one] at hb
  rw [hT] at hb
  obtain ⟨f,g,hcommon,hg,hf,hprob,_⟩ := hb
  refine ⟨f,g,hcommon,hg,hf,?_,hprob⟩
  simpa using count_of_probability_min (2 ^ d) (Fintype.card F) _ c 1
    (Fintype.card_pos) (by simpa using hprob)


/-- The superquadratic growth sentence after Theorem 6.10, in a finite
quantified form. For each requested multiple `R` of `N²`, sufficiently large
domains and `q/N³≥R/c` admit a single pair with at least `R N²` nonzero
challenges. Thus any family with `q/N³→∞` has superquadratic guarantees. -/
theorem half_rate_decision_trees_superquadratic (h : ℕ) (hh : 3 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 0 < R → ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d →
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] (D : AddSubgroup F),
        (additiveDomain D).card = 2 ^ d → 2 ^ d < Fintype.card F →
        (R/c) * (((2 ^ d : ℕ) : ℝ)^3) ≤ Fintype.card F →
        let A := additiveDomain D
        let N : ℕ := 2 ^ d
        let K : ℕ := N / 2
        let T : ℕ := K + N / 2 ^ (h + 1)
        ∃ f g : A → F,
          commonAgreementEQ A K f g K ∧ agreementEQ A K g K ∧
          agreementLE A K f (T - 1) ∧
          R * (N : ℝ)^2 ≤ (nonzeroBadChallenges A K f g T).card := by
  obtain ⟨c,hc,d₁,hbound⟩ := half_rate_decision_trees_probability h (by omega)
  refine ⟨c,hc,?_⟩
  intro R hR
  obtain ⟨r,hr⟩ := exists_nat_gt (R/c)
  have hrpow : R/c < (2 : ℝ)^r := hr.trans_le (by exact_mod_cast (show r < 2^r from Nat.lt_two_pow_self).le)
  refine ⟨max d₁ (max (2^h-1) r),?_⟩
  intro d hd F _ _ _ D hD hq hlarge
  have hd₁ : d₁ ≤ d := (le_max_left _ _).trans hd
  have hth : 2^h-1 ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hrd : r ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hb := hbound d hd₁ hth F D hD hq
  dsimp only at hb
  obtain ⟨f,g,hcommon,hg,hf,hprob,_⟩ := hb
  refine ⟨f,g,hcommon,hg,hf,?_⟩
  have hcount := count_of_probability_min (2 ^ d) (Fintype.card F) _ c
    (2^h-h-1) Fintype.card_pos hprob
  let n : ℝ := (2 ^ d : ℕ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast Nat.one_le_two_pow
  have hRn : R/c ≤ n := by
    apply hrpow.le.trans
    dsimp [n]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hrd
  have he : 3 ≤ 2^h-h-1 := by
    have hp : ∀ j : ℕ, 3 ≤ j → j+5 ≤ 2^j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => decide
      | succ j hj ih => rw [pow_succ]; omega
    have := hp h hh
    omega
  have hfirst : (R/c)*n^2 ≤ n^(2^h-h-1) := by
    apply le_trans ?_ (pow_le_pow_right₀ hn1 he)
    have := mul_le_mul_of_nonneg_right hRn (sq_nonneg n)
    nlinarith only [this]
  have hsecond : (R/c)*n^2 ≤ (Fintype.card F : ℝ)/n := by
    apply (le_div_iff₀ hn).mpr
    change (R/c)*n^3 ≤ Fintype.card F at hlarge
    nlinarith only [hlarge]
  have hmin := mul_le_mul_of_nonneg_left (le_min hfirst hsecond) hc.le
  have heq : c*((R/c)*n^2)=R*n^2 := by field_simp
  rw [heq] at hmin
  exact hmin.trans hcount

/-- The arithmetic of the three heights listed after Theorem 6.10: the
exceptional-count exponents are `4,11,26`, minimum dimensions `7,15,31`,
and agreement fractions `9/16,17/32,33/64`. -/
theorem tree_height_three_four_five_parameters :
    (2^3-3-1 : ℕ)=4 ∧ (2^4-4-1 : ℕ)=11 ∧ (2^5-5-1 : ℕ)=26 ∧
    (2^3-1 : ℕ)=7 ∧ (2^4-1 : ℕ)=15 ∧ (2^5-1 : ℕ)=31 ∧
    (1/2+1/(2 : ℚ)^(3+1))=9/16 ∧
    (1/2+1/(2 : ℚ)^(4+1))=17/32 ∧
    (1/2+1/(2 : ℚ)^(5+1))=33/64 := by norm_num

end BinaryFieldCounterexamples
