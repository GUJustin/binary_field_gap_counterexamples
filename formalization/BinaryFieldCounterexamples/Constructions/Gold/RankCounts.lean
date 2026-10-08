/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.TensorBorder
public import BinaryFieldCounterexamples.Constructions.Gold.BorderedRank
public import BinaryFieldCounterexamples.Constructions.Gold.AlternatingFourier
public import BinaryFieldCounterexamples.Counting.AlternatingRankFormula
/-!
# Actual finite alternating-tensor rank populations

The tensor border equivalence decomposes the literal finite rank class into
old tensors and border vectors. The proved matrix rank update and exact range
cardinality give its counting recurrence. Solving this recurrence supplies the
original Gaussian product formula, with both parities and all boundary ranks.

The zero-frequency character sum is this actual population. Gaussian flag
counting and Newton expansion then prove the weighted zero-frequency identity
needed in the Gold population argument. No counting recurrence is assumed by
these final endpoints.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
/-- The actual finite number of alternating binary tensors of rank twice the index. -/
noncomputable def alternatingTensorRankCount (d j : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun A : TensorIndex d → ZMod 2 => (tensorAlternatingMatrix A).rank=2*j).card
/-- Rank zero consists of the literal zero tensor. -/
theorem alternatingTensorRankCount_zero (d : ℕ) : alternatingTensorRankCount d 0=1 := by
  classical
  have hz (A : TensorIndex d → ZMod 2) : (tensorAlternatingMatrix A).rank=0 ↔ A=0 := by
    rw [matrix_rank_zero_iff,←tensorAlternatingMatrix_zero d]
    exact tensorAlternatingMatrix_injective.eq_iff
  have he : (Finset.univ.filter fun A : TensorIndex d → ZMod 2 => (tensorAlternatingMatrix A).rank=2*0)={0} := by
    ext A
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mul_zero,hz,Finset.mem_singleton]
  unfold alternatingTensorRankCount
  rw [he,Finset.card_singleton]
/-- The dimension bounds every actual alternating tensor rank. -/
theorem alternatingTensorRankCount_vanish (d j : ℕ) (hj : d<2*j) :
    alternatingTensorRankCount d j=0 := by
  classical
  unfold alternatingTensorRankCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro A hA hr
  have hle := (tensorAlternatingMatrix A).rank_le_card_width
  simp only [Fintype.card_fin] at hle
  omega
/-- Dimension zero has no positive-rank tensors. -/
theorem alternatingTensorRankCount_base (j : ℕ) : alternatingTensorRankCount 0 (j+1)=0 := by
  exact alternatingTensorRankCount_vanish 0 (j+1) (by omega)
/-- The cardinality of a binary matrix's range is the exact power of its rank. -/
theorem card_matrix_binary_range (d : ℕ) (C : Matrix (Fin d) (Fin d) (ZMod 2)) :
    Nat.card (LinearMap.range C.mulVecLin)=2^C.rank := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  rw [show Nat.card (ZMod 2)=2 by rw [Nat.card_eq_fintype_card,ZMod.card]]
  rfl
/-- Border vectors in the matrix range form a set of the prescribed rank cardinality. -/
theorem card_filter_matrix_binary_range (d : ℕ) (C : Matrix (Fin d) (Fin d) (ZMod 2)) :
    (Finset.univ.filter fun v : Fin d → ZMod 2 => v ∈ LinearMap.range C.mulVecLin).card=2^C.rank := by
  classical
  rw [←Fintype.card_subtype]
  simpa only [Nat.card_eq_fintype_card] using card_matrix_binary_range d C
/-- The exact complement count for border vectors outside a matrix range. -/
theorem card_filter_not_matrix_binary_range (d : ℕ) (C : Matrix (Fin d) (Fin d) (ZMod 2)) :
    (Finset.univ.filter fun v : Fin d → ZMod 2 => v ∉ LinearMap.range C.mulVecLin).card=2^d-2^C.rank := by
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v : Fin d → ZMod 2 => v ∈ LinearMap.range C.mulVecLin)
  rw [card_filter_matrix_binary_range,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] at hh
  omega
/-- Count a rank fiber from the two possible bordered ranks. -/
theorem count_border_rank_fiber (d j : ℕ) (C : Matrix (Fin d) (Fin d) (ZMod 2))
    (r : (Fin d → ZMod 2) → ℕ)
    (hin : ∀ v, v ∈ LinearMap.range C.mulVecLin → r v=C.rank)
    (hout : ∀ v, v ∉ LinearMap.range C.mulVecLin → r v=C.rank+2) :
    (Finset.univ.filter fun v => r v=2*(j+1)).card=
      (if C.rank=2*(j+1) then 2^C.rank else 0)+
      (if C.rank=2*j then 2^d-2^C.rank else 0) := by
  have hpoint (v : Fin d → ZMod 2) :
      (if r v=2*(j+1) then 1 else 0 : ℕ)=
        (if C.rank=2*(j+1) then (if v ∈ LinearMap.range C.mulVecLin then 1 else 0) else 0)+
        (if C.rank=2*j then (if v ∉ LinearMap.range C.mulVecLin then 1 else 0) else 0) := by
    by_cases hv : v ∈ LinearMap.range C.mulVecLin
    · rw [hin v hv]
      simp [hv]
    · rw [hout v hv]
      simp only [hv,ite_false,not_false_eq_true,ite_true,ite_self,zero_add]
      split_ifs <;> omega
  rw [Finset.card_filter]
  simp_rw [hpoint,Finset.sum_add_distrib,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [←Finset.card_filter,←Finset.card_filter,card_filter_matrix_binary_range,card_filter_not_matrix_binary_range]
/-- Reindexing by the border equivalence decomposes the actual rank count into old-tensor fibers. -/
theorem alternatingTensorRankCount_border_sum (d j : ℕ) :
    alternatingTensorRankCount (d+1) j=
      ∑ A : TensorIndex d → ZMod 2,
        (Finset.univ.filter fun v : Fin d → ZMod 2 =>
          (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (A,v))).rank=2*j).card := by
  unfold alternatingTensorRankCount
  rw [Finset.card_filter]
  rw [←Equiv.sum_comp (tensorBorderEquiv d).symm.toEquiv,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.card_filter]
  rfl
/-- The actual border fibers yield the rank-count recurrence from their two-case matrix update. -/
theorem alternatingTensorRankCount_succ_of_border (d j : ℕ)
    (hborder : ∀ (A : TensorIndex d → ZMod 2) (v : Fin d → ZMod 2),
      let C := tensorAlternatingMatrix A
      let r := (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (A,v))).rank
      (v ∈ LinearMap.range C.mulVecLin → r=C.rank) ∧
      (v ∉ LinearMap.range C.mulVecLin → r=C.rank+2)) :
    alternatingTensorRankCount (d+1) (j+1)=
      4^(j+1)*alternatingTensorRankCount d (j+1)+(2^d-4^j)*alternatingTensorRankCount d j := by
  rw [alternatingTensorRankCount_border_sum]
  have hfiber (A : TensorIndex d → ZMod 2) :
      (Finset.univ.filter fun v : Fin d → ZMod 2 =>
        (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (A,v))).rank=2*(j+1)).card=
        (if (tensorAlternatingMatrix A).rank=2*(j+1) then 4^(j+1) else 0)+
        (if (tensorAlternatingMatrix A).rank=2*j then 2^d-4^j else 0) := by
    rw [count_border_rank_fiber d j (tensorAlternatingMatrix A) _
      (fun v => (hborder A v).1) (fun v => (hborder A v).2)]
    have hp (i : ℕ) : (2:ℕ)^(2*i)=4^i := by rw [pow_mul]; rfl
    apply congrArg₂ (· + ·)
    · split_ifs with h
      · rw [h,hp]
      · rfl
    · split_ifs with h
      · rw [h,hp]
      · rfl
  simp_rw [hfiber]
  rw [Finset.sum_add_distrib]
  simp only [←Finset.sum_filter,Finset.sum_const,smul_eq_mul,alternatingTensorRankCount,mul_comm]
/-- The actual finite alternating-tensor counts obey the bordered-rank recurrence. -/
theorem alternatingTensorRankCount_succ (d j : ℕ) :
    alternatingTensorRankCount (d+1) (j+1)=
      4^(j+1)*alternatingTensorRankCount d (j+1)+(2^d-4^j)*alternatingTensorRankCount d j := by
  apply alternatingTensorRankCount_succ_of_border
  intro A v
  dsimp only
  have hs (i k : Fin d) : tensorAlternatingMatrix A i k=tensorAlternatingMatrix A k i := by
    exact congrFun (congrFun (tensorAlternatingMatrix_transpose A).symm i) k
  have hb := borderedAlternatingMatrix_rank_cases (tensorAlternatingMatrix A) hs
    (tensorAlternatingMatrix_alternating A) v
  have hr : (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (A,v))).rank=
      (borderedAlternatingMatrix (tensorAlternatingMatrix A) v).rank := by
    rw [tensorBorder_matrix_rank]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  rw [hr]
  simp only [Matrix.toLin'_apply'] at hb
  rcases hb with ⟨hv,hr⟩ | ⟨hv,hr⟩
  · exact ⟨fun _ => hr,fun hn => False.elim (hn hv)⟩
  · exact ⟨fun hn => False.elim (hv hn),fun _ => hr⟩
/-- Exact Gaussian product formula for the actual finite alternating-tensor population. -/
theorem alternatingTensorRankCount_eq_product (d j : ℕ) :
    (alternatingTensorRankCount d j:ℚ)=(gaussianBinomial 4 (d/2) j:ℚ)*
      ∏ i ∈ Finset.range j, ((2:ℚ)^(d-(if d%2=0 then 1 else 0))-4^i) := by
  exact alternatingRankNatSequence_formula alternatingTensorRankCount
    alternatingTensorRankCount_zero alternatingTensorRankCount_base
    alternatingTensorRankCount_vanish alternatingTensorRankCount_succ d j
/-- At the zero tensor the actual Fourier class sum is its literal finite population. -/
theorem alternatingRankCharacterSum_at_zero (d j : ℕ) :
    alternatingRankCharacterSum d j 0=(alternatingTensorRankCount d j:ℤ) := by
  simp only [alternatingRankCharacterSum,alternatingTensorRankCount,Finset.card_filter,
    Nat.cast_sum,dotProduct_zero,BinaryQuadraticData.binarySign_zero]
  apply Finset.sum_congr rfl
  intro A hA
  split_ifs <;> rfl
/-- Flag counting and Newton expansion evaluate the weighted product sum. -/
theorem gaussianBinomial_weighted_newton (n s : ℕ) (hs : s≤n) (γ : ℚ) :
    (∑ j ∈ Finset.range (s+1), (gaussianBinomial 4 (n-j) (s-j):ℚ)*
      ((gaussianBinomial 4 n j:ℚ)*gaussianNewtonProduct 4 γ j))=
      γ^s*(gaussianBinomial 4 n s:ℚ) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (s+1)) :
      (gaussianBinomial 4 (n-j) (s-j):ℚ)*((gaussianBinomial 4 n j:ℚ)*gaussianNewtonProduct 4 γ j)=
        (gaussianBinomial 4 n s:ℚ)*((gaussianBinomial 4 s j:ℚ)*gaussianNewtonProduct 4 γ j) := by
    have hj : j≤s := by have := Finset.mem_range.mp hj; omega
    have hf := gaussianBinomial_flag 4 n s j (by decide) hs hj
    have hf' : (gaussianBinomial 4 n s:ℚ)*(gaussianBinomial 4 s j:ℚ)=
        (gaussianBinomial 4 n j:ℚ)*(gaussianBinomial 4 (n-j) (s-j):ℚ) := by exact_mod_cast hf
    linear_combination -gaussianNewtonProduct 4 γ j * hf'
  rw [Finset.sum_congr rfl hterm,←Finset.mul_sum]
  have hn := gaussianBinomial_newton 4 s (by decide) γ
  change (∑ j ∈ Finset.range (s+1), (gaussianBinomial 4 s j:ℚ)*gaussianNewtonProduct 4 γ j)=γ^s at hn
  rw [hn,mul_comm]
/-- The exact weighted zero-frequency identity for actual alternating tensors. -/
theorem alternatingTensorRankCount_weighted (d s : ℕ) (hs : s≤d/2) :
    (∑ j ∈ Finset.range (s+1), (gaussianBinomial 4 (d/2-j) (s-j):ℚ)*
      (alternatingTensorRankCount d j:ℚ))=
      ((2:ℚ)^(d-(if d%2=0 then 1 else 0)))^s*(gaussianBinomial 4 (d/2) s:ℚ) := by
  simp_rw [alternatingTensorRankCount_eq_product]
  exact gaussianBinomial_weighted_newton (d/2) s hs _
end BinaryFieldCounterexamples.Gold
