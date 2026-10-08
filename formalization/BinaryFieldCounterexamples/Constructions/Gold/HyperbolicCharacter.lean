/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicAugment
public import BinaryFieldCounterexamples.Constructions.Gold.RankCounts
/-!
# Hyperbolic recurrence for alternating rank characters
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
open Matrix
open BinaryQuadraticData
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A filtered character sum over a submodule is the usual orthogonality value. -/
theorem sum_binarySign_filter_submodule {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (S : Submodule (ZMod 2) V)
    (l : Module.Dual (ZMod 2) V) :
    (∑ x : V, if x ∈ S then binarySign (l x) else 0) =
      if l.comp S.subtype=0 then (Nat.card S : ℤ) else 0 := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter fun x : V => x ∈ S)]
  · exact BinaryFieldCounterexamples.sum_binarySign_submodule S l
  · intro x
    simp

/-- The total of a nontrivial coordinate character on a binary vector space is zero. -/
theorem sum_binarySign_coordinate_zero (d : ℕ) (i : Fin d) :
    (∑ v : Fin d → ZMod 2, binarySign (v i))=0 := by
  let l : Module.Dual (ZMod 2) (Fin d → ZMod 2) := LinearMap.proj i
  have hl : l ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (Pi.single i 1)
    simp [l] at hh
  exact sum_binarySign_linear_eq_zero l hl

/-- The signed complement of a submodule is the negative of its signed sum. -/
theorem sum_binarySign_not_mem_submodule_coordinate (d : ℕ) (i : Fin d)
    (S : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    (∑ v : Fin d → ZMod 2, if v ∉ S then binarySign (v i) else 0) =
      -(∑ v : Fin d → ZMod 2, if v ∈ S then binarySign (v i) else 0) := by
  have hzero := sum_binarySign_coordinate_zero d i
  have hsplit : (∑ v : Fin d → ZMod 2, binarySign (v i)) =
      (∑ v : Fin d → ZMod 2, if v ∈ S then binarySign (v i) else 0) +
      (∑ v : Fin d → ZMod 2, if v ∉ S then binarySign (v i) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : v ∈ S <;> simp [h]
  omega


/-- A functional vanishes on a map's range exactly when its composite with the map vanishes. -/
theorem comp_range_subtype_eq_zero_iff {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (f : V →ₗ[ZMod 2] W) (l : Module.Dual (ZMod 2) W) :
    l.comp (LinearMap.range f).subtype=0 ↔ l.comp f=0 := by
  constructor
  · intro h
    ext x
    have hx := LinearMap.congr_fun h ⟨f x,⟨x,rfl⟩⟩
    exact hx
  · intro h
    ext z
    obtain ⟨x,hx⟩ := z.property
    have hz := LinearMap.congr_fun h x
    change l (z : W)=0
    rw [←hx]
    exact hz

/-- For a tensor border, the last coordinate vanishes on the matrix range
exactly when the border vector is zero. -/
theorem lastCoordinate_comp_range_zero_iff (d : ℕ)
    (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) :
    let C := tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))
    (LinearMap.proj (Fin.last d)).comp (LinearMap.range C.mulVecLin).subtype=0 ↔ w=0 := by
  dsimp only
  rw [comp_range_subtype_eq_zero_iff]
  constructor
  · intro h
    funext i
    have hi := LinearMap.congr_fun h (Pi.single i.castSucc 1)
    change (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w)) *ᵥ
      Pi.single i.castSucc 1) (Fin.last d)=0 at hi
    rw [Matrix.mulVec_single_one] at hi
    change tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))
      (Fin.last d) i.castSucc=0 at hi
    have hs : tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))
        (Fin.last d) i.castSucc =
        tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))
          i.castSucc (Fin.last d) := by
      simpa only [Matrix.transpose_apply] using congrFun (congrFun
        (tensorAlternatingMatrix_transpose ((tensorBorderEquiv d).symm (B,w)))
        i.castSucc) (Fin.last d)
    change w i=0
    rw [hs, tensorBorder_matrix_last, LinearEquiv.apply_symm_apply] at hi
    exact hi
  · rintro rfl
    apply LinearMap.ext
    intro x
    change (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,0)) *ᵥ x)
      (Fin.last d)=0
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j hj
    have hz : tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,0))
        (Fin.last d) j=0 := by
      refine Fin.lastCases (tensorAlternatingMatrix_diagonal _ _) (fun i => ?_) j
      have hs : tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,0))
          (Fin.last d) i.castSucc =
          tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,0))
            i.castSucc (Fin.last d) := by
        simpa only [Matrix.transpose_apply] using congrFun (congrFun
          (tensorAlternatingMatrix_transpose ((tensorBorderEquiv d).symm (B,0)))
          i.castSucc) (Fin.last d)
      rw [hs, tensorBorder_matrix_last, LinearEquiv.apply_symm_apply]
      rfl
    rw [hz,zero_mul]


/-- The signed range sum for a bordered tensor is nonzero exactly for a zero border. -/
theorem sum_binarySign_last_in_tensor_range (d : ℕ)
    (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) :
    let C := tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))
    (∑ v : Fin (d+1) → ZMod 2,
      if v ∈ LinearMap.range C.mulVecLin then binarySign (v (Fin.last d)) else 0) =
      if w=0 then (2 : ℤ)^C.rank else 0 := by
  dsimp only
  let S := LinearMap.range
    (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))).mulVecLin
  let l : Module.Dual (ZMod 2) (Fin (d+1) → ZMod 2) := LinearMap.proj (Fin.last d)
  have horth := sum_binarySign_filter_submodule S l
  change (∑ v : Fin (d+1) → ZMod 2,
      if v ∈ LinearMap.range
        (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))).mulVecLin then
        binarySign (v (Fin.last d)) else 0) =
      if (LinearMap.proj (Fin.last d)).comp
        (LinearMap.range
          (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))).mulVecLin).subtype=0
      then (Nat.card S : ℤ) else 0 at horth
  have hz := lastCoordinate_comp_range_zero_iff d B w
  dsimp only at hz
  simp only [hz] at horth
  rw [horth]
  split_ifs with h
  · exact_mod_cast card_matrix_binary_range (d+1)
      (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w)))
  · rfl

/-- The signed complement range sum has the opposite value. -/
theorem sum_binarySign_last_not_in_tensor_range (d : ℕ)
    (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) :
    let C := tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))
    (∑ v : Fin (d+1) → ZMod 2,
      if v ∉ LinearMap.range C.mulVecLin then binarySign (v (Fin.last d)) else 0) =
      -(if w=0 then (2 : ℤ)^C.rank else 0) := by
  dsimp only
  rw [sum_binarySign_not_mem_submodule_coordinate,
    sum_binarySign_last_in_tensor_range]


/-- Adding a tensor border preserves rank for a border vector in the old range. -/
theorem tensorBorder_rank_of_mem_range (d : ℕ)
    (C : TensorIndex d → ZMod 2) (v : Fin d → ZMod 2)
    (hv : v ∈ LinearMap.range (tensorAlternatingMatrix C).mulVecLin) :
    (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (C,v))).rank =
      (tensorAlternatingMatrix C).rank := by
  have hs (i k : Fin d) : tensorAlternatingMatrix C i k=tensorAlternatingMatrix C k i := by
    exact congrFun (congrFun (tensorAlternatingMatrix_transpose C).symm i) k
  have hb := borderedAlternatingMatrix_rank_cases (tensorAlternatingMatrix C) hs
    (tensorAlternatingMatrix_alternating C) v
  have hr : (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (C,v))).rank=
      (borderedAlternatingMatrix (tensorAlternatingMatrix C) v).rank := by
    rw [tensorBorder_matrix_rank]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  rw [hr]
  simp only [Matrix.toLin'_apply'] at hb
  rcases hb with h | h
  · exact h.2
  · exact False.elim (h.1 hv)

/-- Adding a tensor border raises rank by two outside the old range. -/
theorem tensorBorder_rank_of_not_mem_range (d : ℕ)
    (C : TensorIndex d → ZMod 2) (v : Fin d → ZMod 2)
    (hv : v ∉ LinearMap.range (tensorAlternatingMatrix C).mulVecLin) :
    (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (C,v))).rank =
      (tensorAlternatingMatrix C).rank+2 := by
  have hs (i k : Fin d) : tensorAlternatingMatrix C i k=tensorAlternatingMatrix C k i := by
    exact congrFun (congrFun (tensorAlternatingMatrix_transpose C).symm i) k
  have hb := borderedAlternatingMatrix_rank_cases (tensorAlternatingMatrix C) hs
    (tensorAlternatingMatrix_alternating C) v
  have hr : (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (C,v))).rank=
      (borderedAlternatingMatrix (tensorAlternatingMatrix C) v).rank := by
    rw [tensorBorder_matrix_rank]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  rw [hr]
  simp only [Matrix.toLin'_apply'] at hb
  rcases hb with h | h
  · exact False.elim (hv h.1)
  · exact h.2

/-- A zero tensor border does not change rank. -/
theorem tensorBorder_rank_zero (d : ℕ) (C : TensorIndex d → ZMod 2) :
    (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (C,0))).rank =
      (tensorAlternatingMatrix C).rank := by
  apply tensorBorder_rank_of_mem_range
  exact Submodule.zero_mem _


/-- The final-border rank fiber splits into its old-range and complementary parts. -/
theorem hyperbolic_final_border_fiber (d j : ℕ)
    (C : TensorIndex (d+1) → ZMod 2) (a : ZMod 2) :
    (∑ v : Fin (d+1) → ZMod 2,
      if (tensorAlternatingMatrix ((tensorBorderEquiv (d+1)).symm (C,v))).rank=2*j
      then binarySign (a+v (Fin.last d)) else 0) =
    binarySign a *
      ((if (tensorAlternatingMatrix C).rank=2*j then
          ∑ v : Fin (d+1) → ZMod 2,
            if v ∈ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
            then binarySign (v (Fin.last d)) else 0
        else 0) +
       (if (tensorAlternatingMatrix C).rank+2=2*j then
          ∑ v : Fin (d+1) → ZMod 2,
            if v ∉ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
            then binarySign (v (Fin.last d)) else 0
        else 0)) := by
  have hpoint (v : Fin (d+1) → ZMod 2) :
      (if (tensorAlternatingMatrix ((tensorBorderEquiv (d+1)).symm (C,v))).rank=2*j
        then binarySign (a+v (Fin.last d)) else 0) =
      binarySign a *
        ((if (tensorAlternatingMatrix C).rank=2*j then
            if v ∈ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
            then binarySign (v (Fin.last d)) else 0 else 0) +
         (if (tensorAlternatingMatrix C).rank+2=2*j then
            if v ∉ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
            then binarySign (v (Fin.last d)) else 0 else 0)) := by
    rw [binarySign_add]
    by_cases hm : v ∈ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
    · rw [tensorBorder_rank_of_mem_range d.succ C v hm]
      simp [hm]
    · rw [tensorBorder_rank_of_not_mem_range d.succ C v hm]
      simp [hm]
  simp_rw [hpoint]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]


/-- The actual rank-class character sums satisfy the canonical hyperbolic recurrence. -/
theorem alternatingRankCharacterSum_hyperbolic (d j : ℕ)
    (A : TensorIndex d → ZMod 2) :
    alternatingRankCharacterSum (d+2) j (hyperbolicAugment d A) =
      (4:ℤ)^j * alternatingRankCharacterSum d j A -
        (if j=0 then 0 else (4:ℤ)^(j-1) * alternatingRankCharacterSum d (j-1) A) := by
  unfold alternatingRankCharacterSum
  rw [← Equiv.sum_comp (tensorBorderEquiv (d+1)).symm.toEquiv,
    Fintype.sum_prod_type]
  have hd (C : TensorIndex (d+1) → ZMod 2) (v : Fin (d+1) → ZMod 2) :
      dotProduct ((tensorBorderEquiv (d+1)).symm.toEquiv (C,v)) (hyperbolicAugment d A) =
        dotProduct (tensorBorderEquiv d C).1 A + v (Fin.last d) := by
    change dotProduct ((tensorBorderEquiv (d+1)).symm (C,v))
      (hyperbolicAugment d A) = _
    simpa only [LinearEquiv.apply_symm_apply] using
      dotProduct_hyperbolicAugment d ((tensorBorderEquiv (d+1)).symm (C,v)) A
  conv_lhs =>
    enter [2, C, 2, v]
    rw [hd C v]
  have hfiber (C : TensorIndex (d+1) → ZMod 2) (a : ZMod 2) :
      (∑ v : Fin (d+1) → ZMod 2,
        if (tensorAlternatingMatrix
          ((tensorBorderEquiv (d+1)).symm.toEquiv (C,v))).rank=2*j
        then binarySign (a+v (Fin.last d)) else 0) =
      binarySign a *
        ((if (tensorAlternatingMatrix C).rank=2*j then
            ∑ v : Fin (d+1) → ZMod 2,
              if v ∈ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
              then binarySign (v (Fin.last d)) else 0 else 0) +
         (if (tensorAlternatingMatrix C).rank+2=2*j then
            ∑ v : Fin (d+1) → ZMod 2,
              if v ∉ LinearMap.range (tensorAlternatingMatrix C).mulVecLin
              then binarySign (v (Fin.last d)) else 0 else 0)) := by
    change (∑ v : Fin (d+1) → ZMod 2,
      if (tensorAlternatingMatrix ((tensorBorderEquiv (d+1)).symm (C,v))).rank=2*j
      then binarySign (a+v (Fin.last d)) else 0) = _
    exact hyperbolic_final_border_fiber d j C a
  simp_rw [hfiber]
  rw [← Equiv.sum_comp (tensorBorderEquiv d).symm.toEquiv,
    Fintype.sum_prod_type]
  have hpair (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) :
      dotProduct (tensorBorderEquiv d ((tensorBorderEquiv d).symm.toEquiv (B,w))).1 A =
        dotProduct B A := by
    change dotProduct (tensorBorderEquiv d ((tensorBorderEquiv d).symm (B,w))).1 A = _
    rw [LinearEquiv.apply_symm_apply]
  have hin (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) :
      let C := tensorAlternatingMatrix ((tensorBorderEquiv d).symm.toEquiv (B,w))
      (∑ v : Fin (d+1) → ZMod 2,
        if v ∈ LinearMap.range C.mulVecLin then binarySign (v (Fin.last d)) else 0) =
        if w=0 then (2:ℤ)^C.rank else 0 := by
    change (∑ v : Fin (d+1) → ZMod 2,
      if v ∈ LinearMap.range
        (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))).mulVecLin
      then binarySign (v (Fin.last d)) else 0) = _
    exact sum_binarySign_last_in_tensor_range d B w
  have hout (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) :
      let C := tensorAlternatingMatrix ((tensorBorderEquiv d).symm.toEquiv (B,w))
      (∑ v : Fin (d+1) → ZMod 2,
        if v ∉ LinearMap.range C.mulVecLin then binarySign (v (Fin.last d)) else 0) =
        -(if w=0 then (2:ℤ)^C.rank else 0) := by
    change (∑ v : Fin (d+1) → ZMod 2,
      if v ∉ LinearMap.range
        (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,w))).mulVecLin
      then binarySign (v (Fin.last d)) else 0) = _
    exact sum_binarySign_last_not_in_tensor_range d B w
  simp_rw [hpair, hin, hout]
  have hzero (B : TensorIndex d → ZMod 2) :
      (tensorAlternatingMatrix ((tensorBorderEquiv d).symm.toEquiv (B,0))).rank =
        (tensorAlternatingMatrix B).rank := by
    change (tensorAlternatingMatrix ((tensorBorderEquiv d).symm (B,0))).rank = _
    exact tensorBorder_rank_zero d B
  let term (B : TensorIndex d → ZMod 2) (w : Fin d → ZMod 2) : ℤ :=
    binarySign (dotProduct B A) *
      ((if (tensorAlternatingMatrix ((tensorBorderEquiv d).symm.toEquiv (B,w))).rank=2*j
        then if w=0 then (2:ℤ)^(tensorAlternatingMatrix
          ((tensorBorderEquiv d).symm.toEquiv (B,w))).rank else 0 else 0) +
       (if (tensorAlternatingMatrix ((tensorBorderEquiv d).symm.toEquiv (B,w))).rank+2=2*j
        then -(if w=0 then (2:ℤ)^(tensorAlternatingMatrix
          ((tensorBorderEquiv d).symm.toEquiv (B,w))).rank else 0) else 0))
  change (∑ B, ∑ w, term B w) = _
  have hcollapse (B : TensorIndex d → ZMod 2) :
      (∑ w, term B w)=term B (0 : Fin d → ZMod 2) := by
    apply Fintype.sum_eq_single
    intro w hw
    simp [term,hw]
  simp_rw [hcollapse]
  simp only [term, hzero, ite_true]
  rcases j with _ | q
  · simp only [mul_zero, ite_true, pow_zero, one_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases h : (tensorAlternatingMatrix B).rank=0
    · simp [h]
    · simp [h]
  · simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    have hp (r : ℕ) : (2:ℤ)^(2*r)=4^r := by
      rw [pow_mul]
      norm_num
    have hterm (B : TensorIndex d → ZMod 2) :
        binarySign (dotProduct B A) *
          ((if (tensorAlternatingMatrix B).rank=2*(q+1)
            then (2:ℤ)^(tensorAlternatingMatrix B).rank else 0) +
           (if (tensorAlternatingMatrix B).rank+2=2*(q+1)
            then -(2:ℤ)^(tensorAlternatingMatrix B).rank else 0)) =
        (4:ℤ)^(q+1) *
          (if (tensorAlternatingMatrix B).rank=2*(q+1)
            then binarySign (dotProduct B A) else 0) -
        (4:ℤ)^q *
          (if (tensorAlternatingMatrix B).rank=2*q
            then binarySign (dotProduct B A) else 0) := by
      by_cases hh : (tensorAlternatingMatrix B).rank=2*(q+1)
      · have hl : (tensorAlternatingMatrix B).rank ≠ 2*q := by omega
        have hs : (tensorAlternatingMatrix B).rank+2 ≠ 2*(q+1) := by omega
        simp only [hh, hl, hs, ite_true, ite_false, add_zero, sub_zero]
        simp only [show 2*(q+1)+2 ≠ 2*(q+1) by omega,
          show 2*(q+1) ≠ 2*q by omega, ite_false, add_zero, mul_zero, sub_zero]
        rw [hp]
        ring
      · by_cases hl : (tensorAlternatingMatrix B).rank=2*q
        · have hs : (tensorAlternatingMatrix B).rank+2=2*(q+1) := by omega
          simp only [hh, hl, hs, ite_true, ite_false, zero_add, mul_zero, zero_sub]
          simp only [show 2*q ≠ 2*(q+1) by omega,
            show 2*q+2 = 2*(q+1) by omega, ite_false, ite_true,
            zero_add, mul_zero, zero_sub]
          rw [hp]
          ring
        · have hs : (tensorAlternatingMatrix B).rank+2 ≠ 2*(q+1) := by omega
          simp [hh, hl, hs]
    simp_rw [hterm, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

end BinaryFieldCounterexamples.Gold
