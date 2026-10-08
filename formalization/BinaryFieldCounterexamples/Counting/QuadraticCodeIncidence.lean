/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.QuadraticComplexMoments
public import BinaryFieldCounterexamples.Counting.QuadraticRankTransform
/-!
# Actual quadratic-code incidence lower bounds

The perfect coordinate pairing and finite Fourier positivity bound the actual
sum of weighted singular-subspace counts over any additive quadratic code.
The canonical-character version has no character-existence premise. The two
specific scalar evaluations needed for the population theorem are separate.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples.QuadraticCoordinates
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype
variable {k : Type*} [Field k] [Fintype k]
/-- Nonnegative matrix-rank weights give the zero-matrix contribution as a code-sum lower bound. -/
theorem quadratic_code_rank_kernel_lower (d : ℕ)
    (C : AddSubgroup (QuadraticForm k (Fin d → k))) [Fintype C]
    (ψ : AddChar k ℂ) (w : ℕ → ℚ) (hw : ∀ r,0≤w r) :
    (w 0 : ℝ) * Fintype.card C ≤
      (∑ Q : C, ∑ M : symmetricMatrices (k:=k) d,
        (w M.val.rank : ℂ) * ψ (matrixPairing d Q M)).re := by
  have hp : (fun M : symmetricMatrices (k:=k) d =>
      ((matrixPairingLinear d).flip M).toAddMonoidHom) 0 = 0 := by ext x; simp
  have h := code_fourier_sum_lower_bound C ψ
    (fun M : symmetricMatrices (k:=k) d => ((matrixPairingLinear d).flip M).toAddMonoidHom)
    hp (fun M => (w M.val.rank : ℝ)) (fun M => by exact_mod_cast hw M.val.rank)
  simpa [matrixPairingLinear] using h

/-- The exact incidence transform transfers the Fourier lower bound to actual singular-subspace counts. -/
theorem quadratic_code_incidence_lower (d : ℕ)
    (C : AddSubgroup (QuadraticForm k (Fin d → k))) [Fintype C]
    (ψ : AddChar k ℂ) (hψ : ψ≠1) (w : ℕ → ℚ) (hw : ∀ r,0≤w r) :
    (w 0 : ℝ) * Fintype.card C ≤
      (∑ Q : C, ∑ e ∈ Finset.range (d+1),
        (gaussianInverseCoefficient (Fintype.card k) d e w : ℝ) *
          ((Fintype.card k) ^ (e*(e+1)/2) : ℕ) *
          (((dimensionSubspaces (k:=k) d e).filter
            (fun W => ∀ x ∈ W, Q.val x=0)).card : ℝ)) := by
  have h := quadratic_code_rank_kernel_lower d C ψ w hw
  simp_rw [quadraticRankWeight_character_transform d w ψ hψ] at h
  norm_cast at h ⊢
  simpa [Complex.mul_re,mul_assoc] using h

/-- Canonical-character incidence lower bound for an actual additive quadratic code. -/
theorem quadratic_code_incidence_lower_canonical (d : ℕ)
    (C : AddSubgroup (QuadraticForm k (Fin d → k))) [Fintype C]
    (w : ℕ → ℚ) (hw : ∀ r,0≤w r) :
    (w 0 : ℝ) * Fintype.card C ≤
      (∑ Q : C, ∑ e ∈ Finset.range (d+1),
        (gaussianInverseCoefficient (Fintype.card k) d e w : ℝ) *
          ((Fintype.card k) ^ (e*(e+1)/2) : ℕ) *
          (((dimensionSubspaces (k:=k) d e).filter
            (fun W => ∀ x ∈ W, Q.val x=0)).card : ℝ)) := by
  exact quadratic_code_incidence_lower d C (AddChar.FiniteField.primitiveChar_to_Complex k)
    (primitiveComplexChar_ne_one k) w hw
end BinaryFieldCounterexamples.QuadraticCoordinates
