/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.BasisCongruence
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicCharacter
public import BinaryFieldCounterexamples.Constructions.Gold.RankCounts
public import BinaryFieldCounterexamples.Counting.GaussianFourierTransform
/-!
# The exact weighted Fourier identity for actual alternating tensors

Strong induction on the actual form dimension uses an orthogonal hyperbolic
splitting whenever the form is nonzero. Basis independence identifies the tensor
with its literal hyperbolic augmentation; the proved character recurrence and
Gaussian Pascal weighting reduce the interior case to the complement. At the
top boundary, the actual rank cutoff supplies the required zero.

The zero form uses the proved finite rank population and Gaussian Newton formula.
The resulting identity has no assumed Fourier or rank-distribution theorem. It
applies to every actual upper-coordinate tensor, with the exact parity-dependent
parameter, including dimension zero and the weight-zero boundary.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
/-- The parity-dependent scalar in the exact alternating Fourier identity. -/
def alternatingFourierParameter (d : ℕ) : ℚ := 2^(d-(if d%2=0 then 1 else 0))
/-- Adding a hyperbolic plane multiplies the parameter by four in positive dimension. -/
theorem alternatingFourierParameter_step (d : ℕ) (hd : 0<d) :
    alternatingFourierParameter (d+2)=4*alternatingFourierParameter d := by
  unfold alternatingFourierParameter
  have he : (d+2)%2=d%2 := by omega
  rw [he]
  split_ifs
  · have hh : d+2-1=(d-1)+2 := by omega
    rw [hh,pow_add]
    ring
  · simp only [Nat.sub_zero,pow_add]
    ring
/-- Rank cutoffs apply to every actual rank-class character sum. -/
theorem alternatingRankCharacterSum_vanish (d j : ℕ) (A : TensorIndex d → ZMod 2) (hj : d<2*j) :
    alternatingRankCharacterSum d j A=0 := by
  unfold alternatingRankCharacterSum
  apply Finset.sum_eq_zero
  intro B hB
  have hl := (tensorAlternatingMatrix B).rank_le_card_width
  simp only [Fintype.card_fin] at hl
  have hn : (tensorAlternatingMatrix B).rank≠2*j := by omega
  simp [hn]
/-- The actual augmented tensor satisfies the Gaussian-weighted rank step. -/
theorem gaussianWeightedSum_hyperbolic (d s : ℕ) (A : TensorIndex d → ZMod 2) (hs : s≤d/2+1) :
    gaussianWeightedSum 4 (d/2+1) s (fun j => (alternatingRankCharacterSum (d+2) j (hyperbolicAugment d A):ℚ))=
      (4:ℚ)^s*gaussianWeightedSum 4 (d/2) s (fun j => (alternatingRankCharacterSum d j A:ℚ)) := by
  apply gaussianWeightedSum_rank_step 4 (d/2) s (by decide) hs
  · rw [alternatingRankCharacterSum_zero,alternatingRankCharacterSum_zero]
  · intro j
    have hh := alternatingRankCharacterSum_hyperbolic d (j+1) A
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel] at hh
    exact_mod_cast hh
/-- Every finite alternating form satisfies the exact weighted Fourier identity in any basis. -/
theorem gaussianWeightedSum_basisTensor
    (d : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hsy : ∀ x y, C x y=C y x) (hal : ∀ x, C x x=0)
    (e : Module.Basis (Fin d) (ZMod 2) V) (s : ℕ) (hs : s≤d/2) :
    gaussianWeightedSum 4 (d/2) s (fun j => (alternatingRankCharacterSum d j (basisTensor C e):ℚ))=
      (alternatingFourierParameter d)^s*
        (gaussianBinomial 4 (d/2-Module.finrank (ZMod 2) (LinearMap.range C)/2) s:ℚ) := by
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    by_cases hsz : s=0
    · subst s
      simp [gaussianWeightedSum,gaussianBinomial,alternatingRankCharacterSum_zero]
    by_cases hC : C=0
    · subst C
      have ht : basisTensor (0 : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) e=0 := by rfl
      rw [ht]
      have hz : Module.finrank (ZMod 2) (LinearMap.range (0 : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V))=0 := by
        rw [LinearMap.range_zero]
        exact finrank_bot (ZMod 2) (Module.Dual (ZMod 2) V)
      rw [hz]
      simpa only [gaussianWeightedSum,alternatingRankCharacterSum_at_zero,Int.cast_natCast,
        alternatingFourierParameter,Nat.zero_div,Nat.sub_zero] using alternatingTensorRankCount_weighted d s hs
    obtain ⟨x,y,hxy⟩ := exists_hyperbolic_pair C hC
    let H := hyperbolicComplement C x y
    let k := Module.finrank (ZMod 2) H
    let C' := hyperbolicRestrictedMap C x y
    let eH := Module.finBasis (ZMod 2) H
    have hd : d=k+2 := by
      have hh := hyperbolicComplement_finrank C x y hsy hal hxy
      change Module.finrank (ZMod 2) V=k+2 at hh
      have he := Module.finrank_eq_card_basis e
      simp only [Fintype.card_fin] at he
      omega
    subst d
    let e' := hyperbolicSplitBasis C x y hsy hal hxy eH
    have hb (j : ℕ) : alternatingRankCharacterSum (k+2) j (basisTensor C e)=
        alternatingRankCharacterSum (k+2) j (hyperbolicAugment k (basisTensor C' eH)) := by
      rw [←basisTensor_hyperbolicSplitBasis C x y hsy hal hxy eH]
      exact alternatingRankCharacterSum_basisTensor_eq C hsy hal e' e j
    have hn : (k+2)/2=k/2+1 := by omega
    have hr := hyperbolicRestrictedMap_rank C x y hsy hal hxy
    have hl : Module.finrank (ZMod 2) (LinearMap.range C')≤k := C'.finrank_range_le
    have hindex : (k+2)/2-Module.finrank (ZMod 2) (LinearMap.range C)/2=
        k/2-Module.finrank (ZMod 2) (LinearMap.range C')/2 := by
      change Module.finrank (ZMod 2) (LinearMap.range C)=Module.finrank (ZMod 2) (LinearMap.range C')+2 at hr
      omega
    have hseq : (fun j => (alternatingRankCharacterSum (k+2) j (basisTensor C e):ℚ))=
        (fun j => (alternatingRankCharacterSum (k+2) j (hyperbolicAugment k (basisTensor C' eH)):ℚ)) := by
      funext j
      rw [hb]
    rw [hseq,hn,gaussianWeightedSum_hyperbolic k s (basisTensor C' eH) (by omega)]
    by_cases hsk : s≤k/2
    · have hh := ih k (by omega) C'
        (hyperbolicRestrictedMap_symmetric C x y hsy) (hyperbolicRestrictedMap_alternating C x y hal) eH hsk
      rw [hh,←hn,hindex,alternatingFourierParameter_step k (by omega)]
      rw [mul_pow]
      ring
    · have he : s=k/2+1 := by omega
      subst s
      rw [gaussianWeightedSum_above]
      rw [alternatingRankCharacterSum_vanish k (k/2+1) (basisTensor C' eH) (by omega),Int.cast_zero,mul_zero]
      have hg : gaussianBinomial 4 ((k/2+1)-Module.finrank (ZMod 2) (LinearMap.range C)/2) (k/2+1)=0 := by
        have hrpos : 2≤Module.finrank (ZMod 2) (LinearMap.range C) := by omega
        simp [gaussianBinomial,show ¬k/2+1≤(k/2+1)-Module.finrank (ZMod 2) (LinearMap.range C)/2 by omega]
      rw [hg,Nat.cast_zero,mul_zero]
/-- The actual alternating tensor character sums satisfy the exact Gaussian weighted identity. -/
theorem gaussianWeightedSum_alternatingTensor (d s : ℕ) (A : TensorIndex d → ZMod 2) (hs : s≤d/2) :
    gaussianWeightedSum 4 (d/2) s (fun j => (alternatingRankCharacterSum d j A:ℚ))=
      (alternatingFourierParameter d)^s*
        (gaussianBinomial 4 (d/2-(tensorAlternatingMatrix A).rank/2) s:ℚ) := by
  let C := matrixPolarMap (tensorAlternatingMatrix A)
  have hM : (tensorAlternatingMatrix A).IsSymm := tensorAlternatingMatrix_transpose A
  have hsy (x y : Fin d → ZMod 2) : C x y=C y x := by
    simp only [C,matrixPolarMap_apply]
    exact hM.dotProduct_mulVec_comm
  have hal (x : Fin d → ZMod 2) : C x x=0 := by
    rw [matrixPolarMap_apply]
    exact tensorAlternatingMatrix_alternating A x
  have hA : basisTensor C (Pi.basisFun (ZMod 2) (Fin d))=A := by
    funext ij
    change matrixPolarMap (tensorAlternatingMatrix A)
      (Pi.basisFun (ZMod 2) (Fin d) ij.val.1) (Pi.basisFun (ZMod 2) (Fin d) ij.val.2)=A ij
    rw [matrixPolarMap_apply_basis]
    have hh := congrFun (congrFun (tensorAlternatingMatrix_transpose A) ij.val.1) ij.val.2
    rw [show tensorAlternatingMatrix A ij.val.2 ij.val.1=tensorAlternatingMatrix A ij.val.1 ij.val.2 from hh,
      tensorAlternatingMatrix_apply_lt A ij.property]
  have h := gaussianWeightedSum_basisTensor d C hsy hal (Pi.basisFun (ZMod 2) (Fin d)) s hs
  rw [hA] at h
  simpa only [C,←matrix_rank_eq_matrixPolarMap_finrank] using h
end BinaryFieldCounterexamples.Gold
