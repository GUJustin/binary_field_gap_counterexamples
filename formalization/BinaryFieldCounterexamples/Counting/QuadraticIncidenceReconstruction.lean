/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SupportedCount
public import BinaryFieldCounterexamples.Counting.GaussianReconstruction

/-!
# Reconstructed quadratic incidence character sums

Support-incidence counts give actual character weights through the proved
restricted symmetric-matrix orthogonality identity. Finite Gaussian inversion
then supplies the unique coefficients of any triangular rank-weight expansion.
No rank/type population or isotropic-subspace enumeration is assumed.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open Module Matrix
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k : Type*} [Field k] [Fintype k]

/-- The number of fixed-dimensional subspaces supporting an actual symmetric matrix. -/
noncomputable def dimensionSupportCount (d e : ℕ)
    (M : symmetricMatrices (k:=k) d) : ℕ :=
  ((dimensionSubspaces (k:=k) d e).filter
    (fun W => M ∈ supportedMatrices d W)).card

/-- The supported-matrix identity written using the literal support-incidence count. -/
theorem dimensionSupportCount_character_sum {R : Type*} [CommRing R] [IsDomain R]
    (d e : ℕ) (ψ : AddChar k R) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (dimensionSupportCount d e M : R) * ψ (matrixPairing d Q M)) =
      (((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : R) *
        (((dimensionSubspaces (k:=k) d e).filter
          (fun W => ∀ x ∈ W, Q x = 0)).card : R) := by
  simpa only [dimensionSupportCount] using
    (weighted_character_isotropic_incidence d e (dimensionSubspaces (k:=k) d e)
      (fun W hW => (mem_dimensionSubspaces d e W).mp hW) ψ hψ Q)

/-- Any finite linear combination of support-incidence weights has an exact
character sum expressed by the corresponding isotropic-subspace counts. -/
theorem weighted_dimensionSupportCount_character_sum
    {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ) (c : ℕ → R) (ψ : AddChar k R) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (∑ e ∈ Finset.range (d + 1), c e * (dimensionSupportCount d e M : R)) *
        ψ (matrixPairing d Q M)) =
      ∑ e ∈ Finset.range (d + 1), c e *
        ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : R) *
          (((dimensionSubspaces (k:=k) d e).filter
            (fun W => ∀ x ∈ W, Q x = 0)).card : R)) := by
  calc
    _ = ∑ M : symmetricMatrices (k:=k) d,
        ∑ e ∈ Finset.range (d + 1),
          (c e * (dimensionSupportCount d e M : R)) * ψ (matrixPairing d Q M) := by
      apply Finset.sum_congr rfl
      intro M hM
      rw [Finset.sum_mul]
    _ = ∑ e ∈ Finset.range (d + 1),
        ∑ M : symmetricMatrices (k:=k) d,
          (c e * (dimensionSupportCount d e M : R)) * ψ (matrixPairing d Q M) := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ Finset.range (d + 1), c e *
        (∑ M : symmetricMatrices (k:=k) d,
          (dimensionSupportCount d e M : R) * ψ (matrixPairing d Q M)) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M hM
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [dimensionSupportCount_character_sum d e ψ hψ Q]

/-- Gaussian inversion supplies the unique support-incidence coefficients in
the actual character-sum identity. -/
theorem reconstructed_dimensionSupportCount_character_sum
    (q d : ℕ) (hq : 1 < q) (c w : ℕ → ℚ)
    (hw : ∀ r ≤ d, w r = gaussianIncidenceTransform q d c r)
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      (∑ e ∈ Finset.range (d + 1),
        (gaussianInverseCoefficient q d e w : ℂ) *
          (dimensionSupportCount d e M : ℂ)) * ψ (matrixPairing d Q M)) =
      ∑ e ∈ Finset.range (d + 1), (c e : ℂ) *
        ((((Fintype.card k) ^ (e * (e + 1) / 2) : ℕ) : ℂ) *
          (((dimensionSubspaces (k:=k) d e).filter
            (fun W => ∀ x ∈ W, Q x = 0)).card : ℂ)) := by
  rw [weighted_dimensionSupportCount_character_sum d
    (fun e => (gaussianInverseCoefficient q d e w : ℂ)) ψ hψ Q]
  apply Finset.sum_congr rfl
  intro e he
  have hed : e ≤ d := by
    have := Finset.mem_range.mp he
    omega
  rw [gaussian_triangular_reconstruction q d hq c w hw e hed]

end BinaryFieldCounterexamples.QuadraticCoordinates
