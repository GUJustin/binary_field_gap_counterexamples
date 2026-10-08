/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.AllRates.Padding
public import BinaryFieldCounterexamples.Counting.BalancedPadding

/-!
# Agreement transfer under balanced nodal padding

Multiplying an input and a witness by the nodal polynomial of a padding set
makes precisely the padding points and the old agreement points into new
agreement points.  The exact identity lets one use a single balanced padding
set for an entire finite family of witnesses.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial Finset

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The agreement set after nodal multiplication is exactly the union of the
padding set with the old agreement set. -/
theorem agreementCount_nodal_mul_eq_card_union
    {F : Type*} [Field F] (D W : Finset F) (hWD : W ⊆ D)
    (f : F → F) (P : F[X]) :
    agreementCount D
        (fun x ↦ (Lagrange.nodal W id).eval (x : F) * f x)
        ((Lagrange.nodal W id) * P) =
      (W ∪ (D.filter fun x ↦ P.eval x = f x)).card := by
  rw [agreementCount_eq_card_filter D
    (fun x ↦ (Lagrange.nodal W id).eval x * f x)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, eval_mul]
  constructor
  · rintro ⟨hxD, hx⟩
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · right
      refine ⟨hxD, ?_⟩
      have hL : (Lagrange.nodal W id).eval x ≠ 0 := by
        intro hz
        exact hxW ((eval_nodal_id_eq_zero_iff W x).1 hz)
      exact (mul_left_cancel₀ hL hx)
  · rintro (hxW | ⟨hxD, hx⟩)
    · refine ⟨hWD hxW, ?_⟩
      rw [(eval_nodal_id_eq_zero_iff W x).2 hxW]
      simp
    · exact ⟨hxD, by rw [hx]⟩

/-- Nodal multiplication adds exactly the padding size to the strict degree
budget. -/
theorem degree_nodal_mul_lt
    {F : Type*} [Field F] (W : Finset F) (K : ℕ) (P : F[X])
    (hP : P.degree < K) :
    ((Lagrange.nodal W id) * P).degree < W.card + K := by
  by_cases hP0 : P = 0
  · simp [hP0]
  · have hPnat := (natDegree_lt_iff_degree_lt hP0).mpr hP
    have hdeg : ((Lagrange.nodal W id) * P).natDegree = W.card + P.natDegree := by
      rw [natDegree_mul Lagrange.nodal_ne_zero hP0,
        Lagrange.natDegree_nodal]
    rw [degree_eq_natDegree (mul_ne_zero Lagrange.nodal_ne_zero hP0), hdeg]
    exact_mod_cast Nat.add_lt_add_left hPnat W.card

/-- Nodal multiplication raises the degree budget by the padding size and
adds the padding set to the old agreement set, with overlap counted once. -/
theorem agreementGE_nodal_padding_overlap
    {F : Type*} [Field F] (D W : Finset F) (hWD : W ⊆ D)
    (K : ℕ) (f : F → F) (P : F[X]) (hP : P.degree < K) :
    agreementGE D (W.card + K)
      (fun x ↦ (Lagrange.nodal W id).eval (x : F) * f x)
      (W.card + agreementCount D (fun x ↦ f x) P -
        (W ∩ (D.filter fun x ↦ P.eval x = f x)).card) := by
  refine ⟨(Lagrange.nodal W id) * P, ?_, ?_⟩
  · exact degree_nodal_mul_lt W K P hP
  · rw [agreementCount_nodal_mul_eq_card_union D W hWD]
    rw [Finset.card_union, agreementCount_eq_card_filter]

/-- A single exact-size padding set simultaneously gives the nodal agreement
lower bound for every witness in a finite family whose old agreement sets all
have the same cardinality. -/
theorem exists_common_nodal_padding
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : Finset F) (I : Finset ι) (f : F → F) (P : ι → F[X])
    (K T w : ℕ)
    (hP : ∀ i ∈ I, (P i).degree < K)
    (hT : ∀ i ∈ I, agreementCount D (fun x ↦ f x) (P i) = T)
    (hwD : w ≤ D.card) :
    ∃ W : Finset F, W ⊆ D ∧ W.card = w ∧ ∀ i ∈ I,
      (Lagrange.nodal W id * P i).degree < w + K ∧
      (w : ℝ) + T -
          ((w : ℝ) * T / D.card +
            Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card))) ≤
        agreementCount D
          (fun x ↦ (Lagrange.nodal W id).eval (x : F) * f x)
          (Lagrange.nodal W id * P i) := by
  let S : ι → Finset F := fun i ↦ D.filter fun x ↦ (P i).eval x = f x
  have hS (i : ι) (hi : i ∈ I) : S i ⊆ D ∧ (S i).card = T := by
    refine ⟨Finset.filter_subset _ _, ?_⟩
    simpa only [S, ← agreementCount_eq_card_filter] using hT i hi
  obtain ⟨W, hWD, hWcard, hbalanced⟩ :=
    exists_balanced_fixedSize_padding D I S T w hS hwD
  refine ⟨W, hWD, hWcard, ?_⟩
  intro i hi
  constructor
  · simpa only [hWcard] using degree_nodal_mul_lt W K (P i) (hP i hi)
  rw [agreementCount_nodal_mul_eq_card_union D W hWD]
  have hcard : ((W ∪ S i).card : ℝ) =
      (w : ℝ) + T - ((W ∩ S i).card : ℝ) := by
    have hu := Finset.card_union_add_card_inter W (S i)
    have hur : ((W ∪ S i).card : ℝ) + (W ∩ S i).card =
        (W.card : ℝ) + (S i).card := by exact_mod_cast hu
    rw [hWcard, (hS i hi).2] at hur
    linarith
  rw [show D.filter (fun x ↦ (P i).eval x = f x) = S i by rfl, hcard]
  linarith [hbalanced i hi]


/-- The common balanced-padding conclusion only needs a lower bound on every
old agreement count.  An equal-size subset of each old agreement set is used
to choose the common padding set. -/
theorem exists_common_nodal_padding_of_agreementGE
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : Finset F) (I : Finset ι) (f : F → F) (P : ι → F[X])
    (K T w : ℕ)
    (hP : ∀ i ∈ I, (P i).degree < K)
    (hT : ∀ i ∈ I, T ≤ agreementCount D (fun x ↦ f x) (P i))
    (hwD : w ≤ D.card) :
    ∃ W : Finset F, W ⊆ D ∧ W.card = w ∧ ∀ i ∈ I,
      (Lagrange.nodal W id * P i).degree < w + K ∧
      (w : ℝ) + T -
          ((w : ℝ) * T / D.card +
            Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card))) ≤
        agreementCount D
          (fun x ↦ (Lagrange.nodal W id).eval (x : F) * f x)
          (Lagrange.nodal W id * P i) := by
  let old : ι → Finset F := fun i ↦ D.filter fun x ↦ (P i).eval x = f x
  have hold (i : ι) (hi : i ∈ I) : T ≤ (old i).card := by
    simpa only [old, ← agreementCount_eq_card_filter] using hT i hi
  let S : ι → Finset F := fun i ↦ if hi : i ∈ I then
    Classical.choose (Finset.exists_subset_card_eq (hold i hi)) else ∅
  have hSsub (i : ι) (hi : i ∈ I) : S i ⊆ old i := by
    simp only [S, dite_eq_left hi]
    exact (Classical.choose_spec (Finset.exists_subset_card_eq (hold i hi))).1
  have hS (i : ι) (hi : i ∈ I) : S i ⊆ D ∧ (S i).card = T := by
    refine ⟨(hSsub i hi).trans (Finset.filter_subset _ _), ?_⟩
    simp only [S, dite_eq_left hi]
    exact (Classical.choose_spec (Finset.exists_subset_card_eq (hold i hi))).2
  obtain ⟨W, hWD, hWcard, hbalanced⟩ :=
    exists_balanced_fixedSize_padding D I S T w hS hwD
  refine ⟨W, hWD, hWcard, ?_⟩
  intro i hi
  constructor
  · simpa only [hWcard] using degree_nodal_mul_lt W K (P i) (hP i hi)
  rw [agreementCount_nodal_mul_eq_card_union D W hWD]
  have hsub : W ∪ S i ⊆ W ∪ old i := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxW | hxS
    · exact Finset.mem_union_left _ hxW
    · exact Finset.mem_union_right _ (hSsub i hi hxS)
  have hcount : ((W ∪ S i).card : ℝ) ≤ ((W ∪ old i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcard : ((W ∪ S i).card : ℝ) =
      (w : ℝ) + T - ((W ∩ S i).card : ℝ) := by
    have hu := Finset.card_union_add_card_inter W (S i)
    have hur : ((W ∪ S i).card : ℝ) + (W ∩ S i).card =
        (W.card : ℝ) + (S i).card := by exact_mod_cast hu
    rw [hWcard, (hS i hi).2] at hur
    linarith
  change _ ≤ ((W ∪ old i).card : ℝ)
  calc
    (w : ℝ) + T -
          ((w : ℝ) * T / D.card +
            Real.sqrt (((w : ℝ) / 2) * Real.log (2 * I.card))) ≤
        ((W ∪ S i).card : ℝ) := by
      rw [hcard]
      linarith [hbalanced i hi]
    _ ≤ ((W ∪ old i).card : ℝ) := hcount

end BinaryFieldCounterexamples
