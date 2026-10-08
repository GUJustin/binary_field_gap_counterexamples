/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Agreement.Interpolation
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Definition 3.5: agreement thresholds and gaps

The maxima below range over actual strict-degree polynomials on the paper's
finite domain. The bridges identify the predicates used by the main theorems
with these maxima. A positive message bound ensures an attaining polynomial,
including when the domain is empty. Real subtraction in the fractional gap
preserves negative gaps instead of truncating them.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- Definitions 3.2 and 3.5: the maximum individual polynomial agreement. -/
noncomputable def paperIndividualAgreement {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) : ℕ := by
  classical
  exact Nat.findGreatest (agreementGE D K w) D.card

/-- Definitions 3.2 and 3.5: maximum agreement on common coordinates. -/
noncomputable def paperCommonAgreement {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) : ℕ := by
  classical
  exact Nat.findGreatest (commonAgreementGE D K f g) D.card

/-- Definition 3.5: exact finite Johnson threshold in coordinates. -/
noncomputable def johnsonCoordinateThreshold (N K : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) * (K - 1 : ℕ))

/-- Definition 3.5: capacity agreement fraction, namely the code rate. -/
noncomputable def capacityAgreementThreshold (N K : ℕ) : ℝ := (K : ℝ) / N

/-- Definition 3.5: deficit from the limiting Johnson fraction, not the finite threshold. -/
noncomputable def johnsonAgreementDeficit (N K : ℕ) (T : ℝ) : ℝ :=
  Real.sqrt (capacityAgreementThreshold N K) - T / N

/-- Definition 3.5: common-agreement gap with real, untruncated subtraction. -/
noncomputable def paperCommonAgreementGap {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℝ) : ℝ :=
  (T - paperCommonAgreement D K f g) / D.card

/-- Definition 3.5: individual distance at the target means strict agreement below it. -/
def individuallyFarAtTarget {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) : Prop :=
  paperIndividualAgreement D K w < T

/-- Definitions 3.2 and 3.5: individual witness counts cannot exceed domain size. -/
theorem thresholdGaps_individual_count_le_card {F : Type*} [Field F]
    (D : Finset F) (w : D → F) (p : F[X]) : agreementCount D w p ≤ D.card := by
  classical
  simpa [agreementCount] using (Code.agree_le_card (u := w) (v := fun x => p.eval x.val))

/-- Definitions 3.2 and 3.5: common witness counts cannot exceed domain size. -/
theorem thresholdGaps_common_count_le_card {F : Type*} [Field F]
    (D : Finset F) (f g : D → F) (p r : F[X]) :
    commonAgreementCount D f g p r ≤ D.card := by
  exact (commonAgreementCount_le_right D f g p r).trans
    (thresholdGaps_individual_count_le_card D g r)

/-- Definition 3.5: the individual maximum is attained for positive message length. -/
theorem paperIndividualAgreement_attained {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (_hK : 0 < K) :
    agreementGE D K w (paperIndividualAgreement D K w) := by
  classical
  apply Nat.findGreatest_spec (Nat.zero_le D.card)
  exact ⟨0, by simp, Nat.zero_le _⟩

/-- Definition 3.5: the common maximum is attained for positive message length. -/
theorem paperCommonAgreement_attained {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (_hK : 0 < K) :
    commonAgreementGE D K f g (paperCommonAgreement D K f g) := by
  classical
  apply Nat.findGreatest_spec (Nat.zero_le D.card)
  exact ⟨0, 0, by simp, by simp, Nat.zero_le _⟩

/-- Definition 3.5: main-theorem individual lower bounds are bounds on the actual maximum. -/
theorem paperIndividualAgreement_ge_iff {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) (hK : 0 < K) :
    T ≤ paperIndividualAgreement D K w ↔ agreementGE D K w T := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, hc⟩ := paperIndividualAgreement_attained D K w hK
    exact ⟨p, hp, h.trans hc⟩
  · intro h
    obtain ⟨p, hp, hc⟩ := h
    exact Nat.le_findGreatest (hc.trans (thresholdGaps_individual_count_le_card D w p)) ⟨p, hp, hc⟩

/-- Definition 3.5: main-theorem common lower bounds are bounds on the actual maximum. -/
theorem paperCommonAgreement_ge_iff {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) (hK : 0 < K) :
    T ≤ paperCommonAgreement D K f g ↔ commonAgreementGE D K f g T := by
  classical
  constructor
  · intro h
    obtain ⟨p, r, hp, hr, hc⟩ := paperCommonAgreement_attained D K f g hK
    exact ⟨p, r, hp, hr, h.trans hc⟩
  · intro h
    obtain ⟨p, r, hp, hr, hc⟩ := h
    exact Nat.le_findGreatest (hc.trans (thresholdGaps_common_count_le_card D f g p r)) ⟨p, r, hp, hr, hc⟩

/-- Definition 3.5: main-theorem individual upper bounds bound the actual maximum. -/
theorem paperIndividualAgreement_le_iff {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) (hK : 0 < K) :
    paperIndividualAgreement D K w ≤ T ↔ agreementLE D K w T := by
  constructor
  · intro h p hp
    exact ((paperIndividualAgreement_ge_iff D K w _ hK).mpr ⟨p, hp, le_rfl⟩).trans h
  · intro h
    obtain ⟨p, hp, hc⟩ := paperIndividualAgreement_attained D K w hK
    exact hc.trans (h p hp)

/-- Definition 3.5: main-theorem common upper bounds bound the actual maximum. -/
theorem paperCommonAgreement_le_iff {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) (hK : 0 < K) :
    paperCommonAgreement D K f g ≤ T ↔ commonAgreementLE D K f g T := by
  constructor
  · intro h p r hp hr
    exact ((paperCommonAgreement_ge_iff D K f g _ hK).mpr ⟨p, r, hp, hr, le_rfl⟩).trans h
  · intro h
    obtain ⟨p, r, hp, hr, hc⟩ := paperCommonAgreement_attained D K f g hK
    exact hc.trans (h p r hp hr)

/-- Definition 3.5: exact individual agreements in the main theorems identify the maximum. -/
theorem paperIndividualAgreement_eq_iff {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) (hK : 0 < K) :
    paperIndividualAgreement D K w = T ↔ agreementEQ D K w T := by
  rw [agreementEQ, ← paperIndividualAgreement_ge_iff D K w T hK,
    ← paperIndividualAgreement_le_iff D K w T hK]
  omega

/-- Definition 3.5: exact common agreements in the main theorems identify the maximum. -/
theorem paperCommonAgreement_eq_iff {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) (hK : 0 < K) :
    paperCommonAgreement D K f g = T ↔ commonAgreementEQ D K f g T := by
  rw [commonAgreementEQ, ← paperCommonAgreement_ge_iff D K f g T hK,
    ← paperCommonAgreement_le_iff D K f g T hK]
  omega

/-- Definition 3.5: an integer upper bound below the target proves individual farness. -/
theorem individuallyFarAtTarget_of_agreementLE {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (C T : ℕ) (hK : 0 < K)
    (h : agreementLE D K w C) (hCT : C < T) : individuallyFarAtTarget D K w T := by
  exact ((paperIndividualAgreement_le_iff D K w C hK).mpr h).trans_lt hCT

/-- Definition 3.5: individual farness is precisely the absence of a target witness. -/
theorem individuallyFarAtTarget_iff_not_agreementGE {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (w : D → F) (T : ℕ) (hK : 0 < K) :
    individuallyFarAtTarget D K w T ↔ ¬ agreementGE D K w T := by
  rw [← paperIndividualAgreement_ge_iff D K w T hK]
  exact lt_iff_not_ge

/-- Definition 3.5: exact common agreement turns the gap into the printed fraction. -/
theorem paperCommonAgreementGap_of_exact {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (C : ℕ) (T : ℝ) (hK : 0 < K)
    (h : commonAgreementEQ D K f g C) :
    paperCommonAgreementGap D K f g T = (T - C) / D.card := by
  rw [paperCommonAgreementGap, (paperCommonAgreement_eq_iff D K f g C hK).mpr h]

/-- Definition 3.5: the main-theorem strict common bound gives a positive fractional gap. -/
theorem paperCommonAgreementGap_pos_of_bound {F : Type*} [Field F]
    (D : Finset F) (K : ℕ) (f g : D → F) (C T : ℕ) (hK : 0 < K)
    (hD : 0 < D.card) (h : commonAgreementLE D K f g C) (hCT : C < T) :
    0 < paperCommonAgreementGap D K f g T := by
  apply div_pos _ (by exact_mod_cast hD)
  apply sub_pos.mpr
  exact_mod_cast ((paperCommonAgreement_le_iff D K f g C hK).mpr h).trans_lt hCT

/-- Definition 3.5: the square-root comparisons used in main theorems express a positive deficit. -/
theorem johnsonAgreementDeficit_pos_iff (N K : ℕ) (T : ℝ) :
    0 < johnsonAgreementDeficit N K T ↔ T / N < Real.sqrt ((K : ℝ) / N) := by
  exact sub_pos

/-- Definition 3.5: finite Johnson-coordinate comparisons have exactly the printed radicand. -/
theorem johnsonCoordinateThreshold_lt_iff (N K : ℕ) (T : ℝ) (hT : 0 < T) :
    johnsonCoordinateThreshold N K < T ↔ (N : ℝ) * (K - 1 : ℕ) < T ^ 2 := by
  exact Real.sqrt_lt' hT

end BinaryFieldCounterexamples
