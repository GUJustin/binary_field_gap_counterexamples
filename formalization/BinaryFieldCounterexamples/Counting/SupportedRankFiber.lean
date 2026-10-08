/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.ContainingSubspaceCount
public import BinaryFieldCounterexamples.Counting.QuadraticIncidenceReconstruction

/-!
# Rank fibers of supported symmetric-matrix incidence

A symmetric matrix is supported on a subspace exactly when its column range is
contained there. The actual support-incidence fiber therefore has the Gaussian
cardinality determined by matrix rank. No quadratic type classification or
isotropic-subspace count is assumed.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticCoordinates
open Module Matrix
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {k : Type*} [Field k] [Fintype k]

/-- Literal column support is equivalent to containment of the matrix column span. -/
theorem mem_supportedMatrices_iff_span_cols_le (d : ℕ)
    (M : symmetricMatrices (k:=k) d) (W : Submodule k (Fin d → k)) :
    M ∈ supportedMatrices d W ↔
      Submodule.span k (Set.range M.val.col) ≤ W := by
  rw [Submodule.span_le]
  constructor
  · intro h x hx
    obtain ⟨j,rfl⟩ := hx
    exact h j
  · intro h j
    exact h (Set.mem_range_self j)

/-- The literal support-incidence fiber is the expected Gaussian coefficient
whenever the requested support dimension lies between the matrix rank and the ambient dimension. -/
theorem dimensionSupportCount_eq_gaussianBinomial_of_rank_le
    (d e : ℕ) (M : symmetricMatrices (k:=k) d)
    (hr : M.val.rank ≤ e) (he : e ≤ d) :
    dimensionSupportCount d e M =
      gaussianBinomial (Fintype.card k) (d - M.val.rank) (e - M.val.rank) := by
  let R := Submodule.span k (Set.range M.val.col)
  have hR : Module.finrank k R = M.val.rank := by
    exact (Matrix.rank_eq_finrank_span_cols M.val).symm
  have hambient : Module.finrank k (Fin d → k) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hc : dimensionSupportCount d e M =
      Nat.card {W : Submodule k (Fin d → k) // R ≤ W ∧ Module.finrank k W = e} := by
    letI : Fintype (Submodule k (Fin d → k)) := Fintype.ofFinite _
    rw [dimensionSupportCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_dimensionSubspaces]
    rw [mem_supportedMatrices_iff_span_cols_le]
    simp only [R, and_comm]
  rw [hc, containingSubspaces_card_eq_gaussianBinomial R e (by simpa [hR] using hr)
    (by simpa [hambient] using he), hR, hambient]

/-- Through the ambient cutoff, the support-incidence fiber depends only on
actual matrix rank, with zero below that rank. -/
theorem dimensionSupportCount_eq_rankWeight
    (d e : ℕ) (M : symmetricMatrices (k:=k) d) (he : e ≤ d) :
    dimensionSupportCount d e M =
      if M.val.rank ≤ e then
        gaussianBinomial (Fintype.card k) (d - M.val.rank) (e - M.val.rank)
      else 0 := by
  by_cases hr : M.val.rank ≤ e
  · rw [ite_eq_left hr]
    exact dimensionSupportCount_eq_gaussianBinomial_of_rank_le d e M hr he
  · rw [ite_eq_right hr]
    rw [dimensionSupportCount]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro W hW
    simp only [Finset.mem_filter, mem_dimensionSubspaces] at hW
    have hle : Submodule.span k (Set.range M.val.col) ≤ W :=
      (mem_supportedMatrices_iff_span_cols_le d M W).mp hW.2
    have hdim := Submodule.finrank_mono hle
    rw [← Matrix.rank_eq_finrank_span_cols M.val, hW.1] at hdim
    exact hr hdim

/-- The supported-incidence character identity regrouped by the actual matrix
rank, with no rank/type population formula. -/
theorem gaussianRankWeight_character_sum
    {R : Type*} [CommRing R] [IsDomain R]
    (d e : ℕ) (he : e ≤ d) (ψ : AddChar k R) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      ((if M.val.rank ≤ e then
          gaussianBinomial (Fintype.card k) (d - M.val.rank) (e - M.val.rank)
        else 0 : ℕ) : R) * ψ (matrixPairing d Q M)) =
      (((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : R) *
        (((dimensionSubspaces (k:=k) d e).filter
          (fun W => ∀ x ∈ W, Q x = 0)).card : R) := by
  simpa only [dimensionSupportCount_eq_rankWeight d e _ he] using
    (dimensionSupportCount_character_sum d e ψ hψ Q)

end BinaryFieldCounterexamples.QuadraticCoordinates
