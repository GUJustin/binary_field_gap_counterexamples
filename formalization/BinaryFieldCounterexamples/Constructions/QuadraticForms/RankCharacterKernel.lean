/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicKernelStep
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicIncidenceRecurrence
public import BinaryFieldCounterexamples.Counting.QuadraticRankTransform
/-!
# Actual exact-rank character sums and Gaussian inverse kernels

The universal rank-weight transform at a literal indicator identifies each
actual symmetric-matrix rank character sum with the rational Gaussian inverse
of actual totally singular incidences. All ranks, including those exceeding
the ambient dimension, are covered without an assumed character identity.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- The inverse Gaussian coefficient of a literal rank indicator. -/
theorem gaussianInverseCoefficient_rank_indicator (q d e r : ℕ) (he : e≤d) :
    gaussianInverseCoefficient q d e (fun j => if j=r then 1 else 0)=
      if e≤r ∧ r≤d then gaussianMobius q (r-e)*(gaussianPascal q (d-e) (r-e):ℚ) else 0 := by
  classical
  unfold gaussianInverseCoefficient
  dsimp only
  by_cases h : e≤r ∧ r≤d
  · rw [ite_eq_left h,Finset.sum_eq_single (r-e)]
    · rw [ite_eq_left (by omega),mul_one]
    · intro a ha hne
      rw [ite_eq_right (by omega),mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ite_eq_right (by have hh := Finset.mem_range.mp ha; omega),mul_zero]
/-- The actual isotropic incidence sequence including its q-power support factor. -/
noncomputable def quadraticIncidenceSequence {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    (Q : QuadraticForm k V) (e : ℕ) : ℚ :=
  (Fintype.card k:ℚ)^(e*(e+1)/2)*(Nat.card (TotallySingularSubspaces Q e):ℚ)
/-- Actual singular counts vanish beyond ambient dimension, without a radical assumption. -/
theorem totallySingularSubspaces_card_zero_of_finrank {k V : Type*}
    [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Q : QuadraticForm k V) (e : ℕ) (he : Module.finrank k V<e) :
    Nat.card (TotallySingularSubspaces Q e)=0 := by
  let : IsEmpty (TotallySingularSubspaces Q e) := ⟨fun S => by
    have h := Submodule.finrank_le S.val
    rw [S.property.1] at h
    omega⟩
  simp
/-- The actual incidence sequence has its ambient-dimension zero tail. -/
theorem quadraticIncidenceSequence_tail {k V : Type*}
    [Field k] [Fintype k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Q : QuadraticForm k V) (e : ℕ) (he : Module.finrank k V<e) :
    quadraticIncidenceSequence Q e=0 := by
  rw [quadraticIncidenceSequence,totallySingularSubspaces_card_zero_of_finrank Q e he]
  simp
end BinaryFieldCounterexamples.QuadraticGeometry
namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open QuadraticGeometry
variable {k : Type*} [Field k] [Fintype k]
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype
attribute [local instance] QuadraticGeometry.totallySingularSubspacesFintype
/-- The actual character sum over symmetric matrices of one exact rank. -/
noncomputable def rankCharacterKernel (d : ℕ) (ψ : AddChar k ℂ)
    (Q : QuadraticForm k (Fin d→k)) (r : ℕ) : ℂ :=
  ∑ M : symmetricMatrices (k:=k) d,if M.val.rank=r then ψ (matrixPairing d Q M) else 0
/-- The literal filtered support count equals the actual totally singular subspace count. -/
theorem dimensionSubspaces_isotropic_card (d e : ℕ) (Q : QuadraticForm k (Fin d→k)) :
    ((dimensionSubspaces (k:=k) d e).filter (fun W => ∀ x ∈ W,Q x=0)).card=
      Nat.card (TotallySingularSubspaces Q e) := by
  symm
  change Nat.card {W : Submodule k (Fin d→k) // Module.finrank k W=e ∧ ∀ x ∈ W,Q x=0}=_
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_of_subtype _ (by intro W; simp only [Finset.mem_filter,mem_dimensionSubspaces])
/-- The actual exact-rank character sum is the literal rational Gaussian inverse of actual singular incidences. -/
theorem rankCharacterKernel_eq_inverse (d r : ℕ) (ψ : AddChar k ℂ) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d→k)) :
    rankCharacterKernel d ψ Q r=
      (rankIncidenceKernel (Fintype.card k) d (quadraticIncidenceSequence Q) r : ℂ) := by
  classical
  by_cases hr : r≤d
  · have ht := quadraticRankWeight_character_transform d (fun j => if j=r then 1 else 0) ψ hψ Q
    have hleft : (∑ M : symmetricMatrices (k:=k) d,
        ((if M.val.rank=r then 1 else 0 : ℚ):ℂ)*ψ (matrixPairing d Q M))=rankCharacterKernel d ψ Q r := by
      apply Finset.sum_congr rfl
      intro M hM
      by_cases h : M.val.rank=r <;> simp [h]
    rw [hleft] at ht
    rw [ht]
    calc
      _ = ∑ e ∈ Finset.range (d+1),if e≤r then
          ((gaussianMobius (Fintype.card k) (r-e)*(gaussianPascal (Fintype.card k) (d-e) (r-e):ℚ)*
            quadraticIncidenceSequence Q e):ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [gaussianInverseCoefficient_rank_indicator _ _ _ _ (by have := Finset.mem_range.mp he; omega),
          dimensionSubspaces_isotropic_card]
        by_cases her : e≤r
        · simp only [her,hr,and_self,↓reduceIte,quadraticIncidenceSequence,Rat.cast_mul,Rat.cast_pow,Nat.cast_pow,Rat.cast_natCast]
        · simp only [her,false_and,↓reduceIte,Rat.cast_zero,zero_mul]
      _ = ∑ e ∈ Finset.range (r+1),
          ((gaussianMobius (Fintype.card k) (r-e)*(gaussianPascal (Fintype.card k) (d-e) (r-e):ℚ)*
            quadraticIncidenceSequence Q e):ℂ) := by
        rw [←Finset.sum_filter]
        congr 1
        ext e
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
      _ = _ := by simp only [rankIncidenceKernel,Rat.cast_sum,Rat.cast_mul]
  · have htail : rankIncidenceKernel (Fintype.card k) d (quadraticIncidenceSequence Q) r=0 := by
      apply rankIncidenceKernel_tail _ _ _ _ _ (by omega)
      intro i hi
      apply quadraticIncidenceSequence_tail
      simpa using hi
    rw [htail,Rat.cast_zero,rankCharacterKernel]
    apply Finset.sum_eq_zero
    intro M hM
    rw [ite_eq_right]
    intro heq
    have hh := M.val.rank_le_card_width
    have hd : M.val.rank≤d := by simpa using hh
    omega
end BinaryFieldCounterexamples.QuadraticCoordinates
