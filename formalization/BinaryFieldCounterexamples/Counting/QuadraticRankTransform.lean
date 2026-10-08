/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.SupportedRankFiber
public import BinaryFieldCounterexamples.Counting.GaussianReconstruction

/-!
# Universal rank-weight character transform

Gaussian inversion rewrites any weight depending only on the rank of a symmetric matrix as
a finite linear combination of literal support-incidence counts. Character orthogonality then
turns those counts into the numbers of totally singular subspaces of a quadratic form. The two
weights used for minimum-rank quadratic codes have the exact incidence cutoffs recorded below.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticCoordinates
open Module Matrix
open scoped BigOperators
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {k : Type*} [Field k] [Fintype k]

/-- The inverse Gaussian coefficients reconstruct a rank weight from the literal
support-incidence fibers of an actual symmetric matrix. -/
theorem inverseCoefficient_support_sum (d : ℕ)
    (w : ℕ → ℚ) (M : symmetricMatrices (k:=k) d) :
    (∑ e ∈ Finset.range (d + 1), gaussianInverseCoefficient (Fintype.card k) d e w *
      (dimensionSupportCount d e M : ℚ)) = w M.val.rank := by
  have hr : M.val.rank ≤ d := by
    simpa using M.val.rank_le_card_width
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hsplit : d + 1 = M.val.rank + (d - M.val.rank + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ e ∈ Finset.range M.val.rank,
        gaussianInverseCoefficient (Fintype.card k) d e w *
          (dimensionSupportCount d e M : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [dimensionSupportCount_eq_rankWeight d e M (by
      have := Finset.mem_range.mp he
      omega)]
    simp only [Finset.mem_range] at he
    rw [ite_eq_right (by omega)]
    simp
  rw [hfirst, zero_add]
  rw [← gaussianIncidenceTransform_inverseCoefficient (Fintype.card k) d M.val.rank hq w hr]
  rw [gaussianIncidenceTransform]
  apply Finset.sum_congr rfl
  intro a ha
  have haD : a ≤ d - M.val.rank := by
    have := Finset.mem_range.mp ha
    omega
  rw [dimensionSupportCount_eq_rankWeight d (M.val.rank + a) M (by omega)]
  rw [ite_eq_left (by omega)]
  rw [gaussianBinomial_eq_gaussianPascal _ _ _ hq]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- Universal actual transform from a matrix-rank character sum to the finite
isotropic-incidence sums with explicit Gaussian inverse coefficients. -/
theorem quadraticRankWeight_character_transform
    (d : ℕ) (w : ℕ → ℚ) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (w M.val.rank : ℂ) * ψ (matrixPairing d Q M)) =
      ∑ e ∈ Finset.range (d + 1),
        (gaussianInverseCoefficient (Fintype.card k) d e w : ℂ) *
          ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) d e).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ)) := by
  rw [← weighted_dimensionSupportCount_character_sum d
    (fun e => (gaussianInverseCoefficient (Fintype.card k) d e w : ℂ)) ψ hψ Q]
  apply Finset.sum_congr rfl
  intro M hM
  have hc :
      (∑ e ∈ Finset.range (d + 1),
        (gaussianInverseCoefficient (Fintype.card k) d e w : ℂ) *
          (dimensionSupportCount d e M : ℂ)) = (w M.val.rank : ℂ) := by
    exact_mod_cast inverseCoefficient_support_sum d w M
  rw [hc]

end BinaryFieldCounterexamples.QuadraticCoordinates

namespace BinaryFieldCounterexamples

/-- The ceiling-rank inverse coefficient vanishes above its exact rank cutoff. -/
theorem quadraticMinusIncidenceCoefficient_eq_zero_of_cutoff
    (q d n t e : ℕ) (ht0 : 0 < t) (htn : t ≤ n) (he : 2 * (n - t) < e) :
    quadraticMinusIncidenceCoefficient q d n t e = 0 := by
  rw [quadraticMinusIncidenceCoefficient, gaussianInverseCoefficient]
  apply Finset.sum_eq_zero
  intro a ha
  rw [quadraticMinusRankWeight]
  have hlt : n - ((e + a + 1) / 2) < t := by omega
  rw [gaussianPascal_eq_zero _ _ _ hlt]
  simp

/-- The floor-rank inverse coefficient vanishes above its exact rank cutoff. -/
theorem quadraticPlusIncidenceCoefficient_eq_zero_of_cutoff
    (q d n t e : ℕ) (ht0 : 0 < t) (htn : t ≤ n) (he : 2 * (n - t) + 1 < e) :
    quadraticPlusIncidenceCoefficient q d n t e = 0 := by
  rw [quadraticPlusIncidenceCoefficient, gaussianInverseCoefficient]
  apply Finset.sum_eq_zero
  intro a ha
  rw [quadraticPlusRankWeight]
  have hlt : n - ((e + a) / 2) < t := by omega
  rw [gaussianPascal_eq_zero _ _ _ hlt]
  simp

end BinaryFieldCounterexamples

namespace BinaryFieldCounterexamples.QuadraticCoordinates

variable {k : Type*} [Field k] [Fintype k]
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype

/-- Universal transform specialized to the safe ceiling rank weight. -/
theorem quadraticMinusRankWeight_character_transform
    (d n t : ℕ) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (quadraticMinusRankWeight (Fintype.card k) n t M.val.rank : ℂ) *
        ψ (matrixPairing d Q M)) =
      ∑ e ∈ Finset.range (d + 1),
        (quadraticMinusIncidenceCoefficient (Fintype.card k) d n t e : ℂ) *
          ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) d e).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ)) := by
  exact quadraticRankWeight_character_transform d
    (quadraticMinusRankWeight (Fintype.card k) n t) ψ hψ Q

/-- Universal transform specialized to the safe floor rank weight. -/
theorem quadraticPlusRankWeight_character_transform
    (d n t : ℕ) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (quadraticPlusRankWeight (Fintype.card k) n t M.val.rank : ℂ) *
        ψ (matrixPairing d Q M)) =
      ∑ e ∈ Finset.range (d + 1),
        (quadraticPlusIncidenceCoefficient (Fintype.card k) d n t e : ℂ) *
          ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) d e).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ)) := by
  exact quadraticRankWeight_character_transform d
    (quadraticPlusRankWeight (Fintype.card k) n t) ψ hψ Q

/-- The ceiling-weight transform has exactly the incidence range allowed by its
rank cutoff. -/
theorem quadraticMinusRankWeight_character_transform_cutoff
    (n t : ℕ) (ht0 : 0 < t) (htn : t ≤ n)
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin (2 * n) → k)) :
    (∑ M : symmetricMatrices (k:=k) (2 * n),
      (quadraticMinusRankWeight (Fintype.card k) n t M.val.rank : ℂ) *
        ψ (matrixPairing (2 * n) Q M)) =
      ∑ e ∈ Finset.range (2 * (n - t) + 1),
        (quadraticMinusIncidenceCoefficient (Fintype.card k) (2 * n) n t e : ℂ) *
          ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) (2 * n) e).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ)) := by
  rw [quadraticMinusRankWeight_character_transform (k:=k) (2 * n) n t ψ hψ Q]
  have hsplit : 2 * n + 1 = (2 * (n - t) + 1) + 2 * t := by omega
  rw [hsplit, Finset.sum_range_add]
  suffices
      (∑ a ∈ Finset.range (2 * t),
        (quadraticMinusIncidenceCoefficient (Fintype.card k) (2 * n) n t
            (2 * (n - t) + 1 + a) : ℂ) *
          ((((Fintype.card k) ^
              ((2 * (n - t) + 1 + a) * (2 * (n - t) + 1 + a + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) (2 * n) (2 * (n - t) + 1 + a)).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ))) = 0 by
    rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro a ha
  rw [quadraticMinusIncidenceCoefficient_eq_zero_of_cutoff
    (Fintype.card k) (2 * n) n t (2 * (n - t) + 1 + a) ht0 htn (by omega)]
  simp

/-- The floor-weight transform has exactly the incidence range allowed by its
rank cutoff. -/
theorem quadraticPlusRankWeight_character_transform_cutoff
    (n t : ℕ) (ht0 : 0 < t) (htn : t ≤ n)
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin (2 * n) → k)) :
    (∑ M : symmetricMatrices (k:=k) (2 * n),
      (quadraticPlusRankWeight (Fintype.card k) n t M.val.rank : ℂ) *
        ψ (matrixPairing (2 * n) Q M)) =
      ∑ e ∈ Finset.range (2 * (n - t) + 2),
        (quadraticPlusIncidenceCoefficient (Fintype.card k) (2 * n) n t e : ℂ) *
          ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) (2 * n) e).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ)) := by
  rw [quadraticPlusRankWeight_character_transform (k:=k) (2 * n) n t ψ hψ Q]
  have hsplit : 2 * n + 1 = (2 * (n - t) + 2) + (2 * t - 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  suffices
      (∑ a ∈ Finset.range (2 * t - 1),
        (quadraticPlusIncidenceCoefficient (Fintype.card k) (2 * n) n t
            (2 * (n - t) + 2 + a) : ℂ) *
          ((((Fintype.card k) ^
              ((2 * (n - t) + 2 + a) * (2 * (n - t) + 2 + a + 1) / 2) : ℕ) : ℂ) *
            (((dimensionSubspaces (k:=k) (2 * n) (2 * (n - t) + 2 + a)).filter
              (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ))) = 0 by
    rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro a ha
  rw [quadraticPlusIncidenceCoefficient_eq_zero_of_cutoff
    (Fintype.card k) (2 * n) n t (2 * (n - t) + 2 + a) ht0 htn (by omega)]
  simp

end BinaryFieldCounterexamples.QuadraticCoordinates
