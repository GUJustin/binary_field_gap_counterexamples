/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.PaperSemantics
public import BinaryFieldCounterexamples.ReciprocalAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement

/-!
# Agreement interfaces for the concrete paper semantics

These bridges use the actual finite coordinate subtype and ArkLib's agreement
sets. They preserve strict polynomial degrees, including the zero message bound.
The common-agreement upper bound is the first step toward the common-agreement gap
in the quadratic construction; attainment requires a separate simultaneous witness.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial
attribute [local instance] Classical.decEq

/-- The paper's agreement count is the cardinality of ArkLib's agreement set. -/
theorem agreementCount_eq_card_polynomialAgreementSet
    {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (w : D → F) (p : F[X]) :
    agreementCount D w p =
      (ReedSolomon.polynomialAgreementSet ⟨Subtype.val, Subtype.val_injective⟩ w p).card := by
  classical
  simp only [agreementCount, Code.agree, ReedSolomon.polynomialAgreementSet]
  congr 1
  ext x
  simp [eq_comm]

/-- Common agreement counts simultaneous matches on the same coordinates. -/
theorem commonAgreementCount_eq_card_commonPolynomialAgreementSet
    {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (f g : D → F) (p r : F[X]) :
    commonAgreementCount D f g p r =
      (ReedSolomon.commonPolynomialAgreementSet
        ⟨Subtype.val, Subtype.val_injective⟩ f g p r).card := by
  classical
  simp only [commonAgreementCount, Code.agree, ReedSolomon.commonPolynomialAgreementSet]
  congr 1
  ext x
  simp [eq_comm]

/-- Forgetting the first explaining polynomial can only increase agreement. -/
theorem commonAgreementCount_le_right
    {F : Type*} [Field F] (D : Finset F) (f g : D → F) (p r : F[X]) :
    commonAgreementCount D f g p r ≤ agreementCount D g r := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact congrArg Prod.snd hx

/-- An individual upper bound also bounds every pair of simultaneous explaining polynomials. -/
theorem commonAgreementLE_of_right
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ)
    (hg : agreementLE D K g T) : commonAgreementLE D K f g T := by
  intro p r _ hr
  exact (commonAgreementCount_le_right D f g p r).trans (hg r hr)

/-- Forgetting the second explaining polynomial can only increase agreement. -/
theorem commonAgreementCount_le_left
    {F : Type*} [Field F] (D : Finset F) (f g : D → F) (p r : F[X]) :
    commonAgreementCount D f g p r ≤ agreementCount D f p := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact congrArg Prod.fst hx

/-- Membership in the exceptional set has exactly the paper's strict-degree semantics. -/
theorem mem_badChallenges
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) (z : F) :
    z ∈ badChallenges D K f g T ↔
      agreementGE D K (fun x ↦ f x + z * g x) T := by
  classical
  simp [badChallenges]

/-- Adding a multiple of the direction to the first input translates every
exceptional challenge by its negative. The explaining polynomials and thresholds stay
unchanged, including the strict message-degree bound. -/
theorem badChallenges_add_direction_eq
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) (a : F) :
    badChallenges D K (fun x ↦ f x + a * g x) g T =
      (badChallenges D K f g T).image (fun z ↦ z - a) := by
  classical
  ext z
  rw [mem_badChallenges]
  simp only [Finset.mem_image, mem_badChallenges]
  have hword : (fun x : D ↦ (f x + a * g x) + z * g x) =
      (fun x : D ↦ f x + (z + a) * g x) := by
    funext x
    ring
  rw [hword]
  constructor
  · intro hz
    exact ⟨z + a, hz, by ring⟩
  · rintro ⟨w, hw, hwz⟩
    have hw' : w = z + a := by linear_combination hwz
    simpa only [hw'] using hw

/-- A change of the first input along its received line preserves the number
of distinct exceptional challenges, even when one of the challenges is zero. -/
theorem card_badChallenges_add_direction
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) (a : F) :
    (badChallenges D K (fun x ↦ f x + a * g x) g T).card =
      (badChallenges D K f g T).card := by
  rw [badChallenges_add_direction_eq]
  exact Finset.card_image_of_injective _ (fun _ _ h ↦ by linear_combination h)

/-- Removing the zero challenge loses at most one distinct challenge. -/
theorem card_badChallenges_sub_one_le_nonzero
    {F : Type*} [Field F] [Fintype F]
    (D : Finset F) (K : ℕ) (f g : D → F) (T : ℕ) :
    (badChallenges D K f g T).card - 1 ≤ (nonzeroBadChallenges D K f g T).card := by
  classical
  by_cases h : 0 ∈ badChallenges D K f g T
  · simp [nonzeroBadChallenges, Finset.card_erase_of_mem h]
  · simp [nonzeroBadChallenges, Finset.erase_eq_of_notMem h]

/-- For an ambient word, the coordinate count is the corresponding domain filter. -/
theorem agreementCount_eq_card_filter
    {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (w : F → F) (p : F[X]) :
    agreementCount D (fun x ↦ w x) p = (D.filter fun x ↦ p.eval x = w x).card := by
  classical
  unfold agreementCount Code.agree
  apply Finset.card_bij (fun x _ ↦ x.val)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_filter.mpr ⟨x.property, hx.symm⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hxD, hx⟩ := Finset.mem_filter.mp hx
    exact ⟨⟨x, hxD⟩, by simpa using hx.symm, rfl⟩

/-- The pole-excluding reciprocal bound in the concrete input semantics. -/
theorem agreementLE_reciprocal
    {F : Type*} [Field F] (D : Finset F) (β : F) (hβ : β ∉ D) (K : ℕ) :
    agreementLE D K (fun x ↦ ((x : F) - β)⁻¹) K := by
  classical
  intro p hp
  rw [agreementCount_eq_card_filter D (fun x ↦ (x - β)⁻¹) p]
  exact reciprocal_agreement_card_le D β hβ p K hp

/-- A nonzero polynomial has at most its degree many roots in any domain. -/
theorem card_filter_eval_eq_zero_le
    {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (p : F[X]) (hp : p ≠ 0) :
    (D.filter fun x ↦ p.eval x = 0).card ≤ p.natDegree := by
  apply (Finset.card_le_card (show (D.filter fun x ↦ p.eval x = 0) ⊆
    p.roots.toFinset from ?_)).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' p))
  intro x hx
  exact Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (Finset.mem_filter.mp hx).2)

/-- A polynomial input above the message degree has its usual root-count bound. -/
theorem agreementLE_polynomial
    {F : Type*} [Field F] (D : Finset F) (K : ℕ) (q : F[X])
    (hq : (K : WithBot ℕ) ≤ q.degree) :
    agreementLE D K (fun x ↦ q.eval x) q.natDegree := by
  classical
  intro p hp
  have hlt : p.degree < q.degree := hp.trans_le hq
  have hne : p - q ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [h] at hlt)
  rw [agreementCount_eq_card_filter D (fun x ↦ q.eval x) p]
  have heq : (D.filter fun x ↦ p.eval x = q.eval x) =
      D.filter (fun x ↦ (p - q).eval x = 0) := by
    ext x
    simp [sub_eq_zero]
  rw [heq]
  have hd : (p - q).degree = q.degree := degree_sub_eq_right_of_degree_lt hlt
  exact (card_filter_eval_eq_zero_le D (p - q) hne).trans_eq
    (natDegree_eq_of_degree_eq hd)

end BinaryFieldCounterexamples
