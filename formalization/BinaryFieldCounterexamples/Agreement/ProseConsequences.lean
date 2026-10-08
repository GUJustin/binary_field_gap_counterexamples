/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.ThresholdGaps
public import BinaryFieldCounterexamples.Polynomial.SectionThreeCanonical

/-!
# Unnumbered consequences of the agreement definitions in Section 3

The common maximum rules out even explaining the inputs on an arbitrary common
set at a larger target. The minima of actual polynomial Hamming distances are
one minus the maximum agreement fraction, including for the pair alphabet.
Their difference is precisely the common-agreement gap of Definition 3.5.
The final example exhibits why canonical reduction can change extension values.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Section 3.1, prose after Definition 3.3: a target above the common upper
bound cannot be explained by any pair of strict-degree polynomials. -/
theorem prose_no_common_target_witness {F : Type*} [Field F]
    (D : Finset F) (K C T : ℕ) (f g : D → F)
    (h : commonAgreementLE D K f g C) (hCT : C < T) :
    ¬ commonAgreementGE D K f g T := by
  rintro ⟨p, r, hp, hr, hc⟩
  exact (not_le_of_gt hCT) (hc.trans (h p r hp hr))

/-- Section 4.2, prose after Theorem 4.5: if all challenges are exceptional,
then the first input itself reaches the target, so is not individually far. -/
theorem prose_all_challenges_first_input_close {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K T : ℕ) (f g : D → F) (hK : 0 < K)
    (h : badChallenges D K f g T = Finset.univ) :
    agreementGE D K f T ∧ ¬ individuallyFarAtTarget D K f T := by
  have hz : (0 : F) ∈ badChallenges D K f g T := by rw [h]; exact Finset.mem_univ _
  have hf : agreementGE D K f T := by simpa using (mem_badChallenges D K f g T 0).mp hz
  exact ⟨hf, fun hn => (individuallyFarAtTarget_iff_not_agreementGE D K f T hK).mp hn hf⟩

/-- Section 3.1, distance prose: an actual polynomial's relative Hamming
error is one minus its agreement fraction on the finite evaluation domain. -/
theorem prose_polynomial_distance_complement {F : Type*} [Field F]
    (D : Finset F) (w : D → F) (p : F[X]) (hD : 0 < D.card) :
    (hammingDist w (fun x => p.eval x.val) : ℝ) / D.card =
      1 - (agreementCount D w p : ℝ) / D.card := by
  classical
  have h : agreementCount D w p + hammingDist w (fun x => p.eval x.val) = D.card := by
    simpa [agreementCount] using
      (Code.agree_add_hammingDist (u := w) (v := fun x => p.eval x.val))
  have hr : (agreementCount D w p : ℝ) + hammingDist w (fun x => p.eval x.val) = D.card := by
    exact_mod_cast h
  have hp : (D.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  field_simp
  linarith

/-- Section 3.1, distance prose: distance to the actual strict-degree code is
attained and equals one minus the maximum individual agreement fraction. -/
theorem prose_individual_distance_isLeast {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (hD : 0 < D.card) (hK : 0 < K) :
    IsLeast {δ : ℝ | ∃ p : F[X], p.degree < K ∧
      δ = (hammingDist w (fun x => p.eval x.val) : ℝ) / D.card}
      (1 - (paperIndividualAgreement D K w : ℝ) / D.card) := by
  classical
  obtain ⟨p, hp, hc⟩ := paperIndividualAgreement_attained D K w hK
  have hm : agreementCount D w p ≤ paperIndividualAgreement D K w :=
    (paperIndividualAgreement_ge_iff D K w _ hK).mpr ⟨p, hp, le_rfl⟩
  refine ⟨⟨p, hp, ?_⟩, ?_⟩
  · rw [prose_polynomial_distance_complement D w p hD, le_antisymm hc hm]
  · rintro δ ⟨r, hr, rfl⟩
    rw [prose_polynomial_distance_complement D w r hD]
    have hn : (agreementCount D w r : ℝ) ≤ paperIndividualAgreement D K w := by
      exact_mod_cast (paperIndividualAgreement_ge_iff D K w _ hK).mpr ⟨r, hr, le_rfl⟩
    exact sub_le_sub_left (div_le_div_of_nonneg_right hn (by positivity)) 1

/-- Section 3.1, common-gap prose: each actual pair codeword has relative
Hamming error one minus its common agreement fraction. -/
theorem prose_interleaved_distance_complement {F : Type*} [Field F]
    (D : Finset F) (f g : D → F) (p r : F[X]) (hD : 0 < D.card) :
    (hammingDist (fun x => (f x, g x)) (fun x => (p.eval x.val, r.eval x.val)) : ℝ) /
      D.card = 1 - (commonAgreementCount D f g p r : ℝ) / D.card := by
  classical
  have h : commonAgreementCount D f g p r +
      hammingDist (fun x => (f x, g x)) (fun x => (p.eval x.val, r.eval x.val)) = D.card := by
    simpa [commonAgreementCount] using (Code.agree_add_hammingDist
      (u := fun x => (f x, g x)) (v := fun x => (p.eval x.val, r.eval x.val)))
  have hr : (commonAgreementCount D f g p r : ℝ) +
      hammingDist (fun x => (f x, g x)) (fun x => (p.eval x.val, r.eval x.val)) = D.card := by
    exact_mod_cast h
  have hp : (D.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  field_simp
  linarith

/-- Section 3.1, common-gap prose: distance to the actual two-word interleaved
code is attained and equals one minus maximum common agreement divided by length. -/
theorem prose_interleaved_distance_isLeast {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (hD : 0 < D.card) (hK : 0 < K) :
    IsLeast {δ : ℝ | ∃ p r : F[X], p.degree < K ∧ r.degree < K ∧
      δ = (hammingDist (fun x => (f x, g x))
        (fun x => (p.eval x.val, r.eval x.val)) : ℝ) / D.card}
      (1 - (paperCommonAgreement D K f g : ℝ) / D.card) := by
  classical
  obtain ⟨p, r, hp, hr, hc⟩ := paperCommonAgreement_attained D K f g hK
  have hm : commonAgreementCount D f g p r ≤ paperCommonAgreement D K f g :=
    (paperCommonAgreement_ge_iff D K f g _ hK).mpr ⟨p, r, hp, hr, le_rfl⟩
  refine ⟨⟨p, r, hp, hr, ?_⟩, ?_⟩
  · rw [prose_interleaved_distance_complement D f g p r hD, le_antisymm hc hm]
  · rintro δ ⟨p, r, hp, hr, rfl⟩
    rw [prose_interleaved_distance_complement D f g p r hD]
    have hn : (commonAgreementCount D f g p r : ℝ) ≤ paperCommonAgreement D K f g := by
      exact_mod_cast (paperCommonAgreement_ge_iff D K f g _ hK).mpr ⟨p, r, hp, hr, le_rfl⟩
    exact sub_le_sub_left (div_le_div_of_nonneg_right hn (by positivity)) 1

/-- Section 3.1, common-gap prose: a target witness makes the combination's
minimum relative distance at most `1-T/N`. -/
theorem prose_combination_distance_le_target {F : Type*} [Field F]
    (D : Finset F) (K T : ℕ) (f g : D → F) (z : F)
    (hD : 0 < D.card) (hK : 0 < K)
    (h : agreementGE D K (fun x => f x + z * g x) T) :
    1 - (paperIndividualAgreement D K (fun x => f x + z * g x) : ℝ) / D.card ≤
      1 - (T : ℝ) / D.card := by
  have hm : (T : ℝ) ≤ paperIndividualAgreement D K (fun x => f x + z * g x) := by
    exact_mod_cast (paperIndividualAgreement_ge_iff D K _ T hK).mpr h
  exact sub_le_sub_left (div_le_div_of_nonneg_right hm (by positivity)) 1

/-- Section 3.1, common-gap prose: permitted loss below the printed gap is
strictly exceeded by the actual difference of minimum relative distances. -/
theorem prose_proximity_loss_exceeded {F : Type*} [Field F]
    (D : Finset F) (K T : ℕ) (f g : D → F) (z : F) (ε : ℝ)
    (hD : 0 < D.card) (hK : 0 < K)
    (h : agreementGE D K (fun x => f x + z * g x) T)
    (hε : ε < paperCommonAgreementGap D K f g T) :
    ε < (1 - (paperCommonAgreement D K f g : ℝ) / D.card) -
      (1 - (paperIndividualAgreement D K (fun x => f x + z * g x) : ℝ) / D.card) := by
  have ht := prose_combination_distance_le_target D K T f g z hD hK h
  unfold paperCommonAgreementGap at hε
  rw [sub_div] at hε
  linarith

/-- Section 3.1, prose after Definition 3.6: two polynomials can represent the
same binary-field function but differ at an extension point outside `0,1`. -/
theorem prose_canonical_reduction_changes_extension_value
    {F : Type*} [Field F] (φ : ZMod 2 →+* F) (β : F) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    (canonicalRepresentative (Finset.univ : Finset (ZMod 2)) (fun _ => 0)) = 0 ∧
    (∀ x : ZMod 2, (X ^ 2 - X : (ZMod 2)[X]).eval x = 0) ∧
    ((X ^ 2 - X : (ZMod 2)[X]).map φ).eval β ≠ (0 : F[X]).eval β := by
  refine ⟨?_, ?_, ?_⟩
  · symm
    apply eq_canonicalRepresentative
    · simp only [degree_zero, Finset.card_univ, ZMod.card]
      exact WithBot.bot_lt_coe 2
    · simp
  · intro x
    simpa using sub_eq_zero.mpr (FiniteField.pow_card x)
  · simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, eval_sub, eval_pow, eval_X, eval_zero]
    rw [show β ^ 2 - β = β * (β - 1) by ring]
    exact mul_ne_zero hβ0 (sub_ne_zero.mpr hβ1)


/-- Section 3.1, line 113: a gap of one coordinate vanishes as length grows,
so it eventually lies below every fixed positive fractional proximity loss. -/
theorem prose_single_coordinate_gap_vanishes (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {F : Type*} [Field F] (D : Finset F) (K C : ℕ) (f g : D → F),
      N₀ ≤ D.card → 0 < K → commonAgreementEQ D K f g C →
      paperCommonAgreementGap D K f g (C + 1 : ℕ) = 1 / (D.card : ℝ) ∧
        paperCommonAgreementGap D K f g (C + 1 : ℕ) < ε := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ε)
  refine ⟨N₀, ?_⟩
  intro F fieldF D K C f g hN hK hc
  have hn : 1 / ε < (D.card : ℝ) := hN₀.trans_le (by exact_mod_cast hN)
  have hp : (0 : ℝ) < D.card := (div_pos (by norm_num) hε).trans hn
  have hg : paperCommonAgreementGap D K f g (C + 1 : ℕ) = 1 / (D.card : ℝ) := by
    rw [paperCommonAgreementGap_of_exact D K f g C _ hK hc]
    push_cast
    ring
  refine ⟨hg, ?_⟩
  rw [hg]
  apply (div_lt_iff₀ hp).mpr
  have hh := (div_lt_iff₀ hε).mp hn
  nlinarith

end BinaryFieldCounterexamples
