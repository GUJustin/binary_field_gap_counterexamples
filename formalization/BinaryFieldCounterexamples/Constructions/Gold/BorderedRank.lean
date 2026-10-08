/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.RankParity
public import Mathlib.LinearAlgebra.Prod

/-!
# Rank of a bordered binary alternating form
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- A linear functional which vanishes on the kernel of a symmetric map to
its dual belongs to that map's range. -/
theorem mem_range_of_forall_mem_ker_eq_zero
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hsym : ∀ x y, C x y = C y x) (v : Module.Dual (ZMod 2) V)
    (hv : ∀ x, C x = 0 → v x = 0) : v ∈ LinearMap.range C := by
  let K := LinearMap.ker C
  have hrange_le : LinearMap.range C ≤ K.dualAnnihilator := by
    intro w hw
    obtain ⟨x, rfl⟩ := hw
    rw [← K.dualRestrict_ker_eq_dualAnnihilator, LinearMap.mem_ker]
    ext y
    rw [Submodule.dualRestrict_apply]
    change C x (y : V) = 0
    rw [hsym]
    have hy : C (y : V) = 0 := y.property
    rw [hy]
    rfl
  have hfin : Module.finrank (ZMod 2) (LinearMap.range C) =
      Module.finrank (ZMod 2) K.dualAnnihilator := by
    have hr := C.finrank_range_add_finrank_ker
    have ha := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    change Module.finrank (ZMod 2) K +
      Module.finrank (ZMod 2) K.dualAnnihilator = Module.finrank (ZMod 2) V at ha
    dsimp [K] at ha ⊢
    omega
  have heq : LinearMap.range C = K.dualAnnihilator :=
    Submodule.eq_of_le_of_finrank_le hrange_le hfin.ge
  rw [heq, ← K.dualRestrict_ker_eq_dualAnnihilator, LinearMap.mem_ker]
  ext x
  rw [Submodule.dualRestrict_apply]
  exact hv x x.property

/-- The bordered map associated with a symmetric binary form and one new
coordinate functional. -/
noncomputable def borderedPolarMap
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (v : Module.Dual (ZMod 2) V) :
    (V × ZMod 2) →ₗ[ZMod 2] (Module.Dual (ZMod 2) V × ZMod 2) :=
  LinearMap.prod
    (C.comp (LinearMap.fst (ZMod 2) V (ZMod 2)) +
      ((LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight v).comp
        (LinearMap.snd (ZMod 2) V (ZMod 2)))
    (v.comp (LinearMap.fst (ZMod 2) V (ZMod 2)))

@[simp] theorem borderedPolarMap_apply
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (v : Module.Dual (ZMod 2) V) (x : V) (a : ZMod 2) :
    borderedPolarMap C v (x, a) = (C x + a • v, v x) := by
  simp [borderedPolarMap]

/-- Outside the old range, the bordered kernel is the kernel of the new
functional restricted to the old kernel. -/
noncomputable def borderedKernelEquiv_of_not_mem_range
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (v : Module.Dual (ZMod 2) V) (hv : v ∉ LinearMap.range C) :
    LinearMap.ker (borderedPolarMap C v) ≃
      LinearMap.ker (v.comp (LinearMap.ker C).subtype) := by
  let f : LinearMap.ker (borderedPolarMap C v) →
      LinearMap.ker (v.comp (LinearMap.ker C).subtype) := fun z ↦ by
    have hz := z.property
    have hfirst := congrArg Prod.fst hz
    have hsecond := congrArg Prod.snd hz
    change C z.val.1 + z.val.2 • v = 0 at hfirst
    change v z.val.1 = 0 at hsecond
    have ha : z.val.2 = 0 := by
      rcases binary_eq_zero_or_one z.val.2 with ha | ha
      · exact ha
      · exfalso
        apply hv
        refine ⟨z.val.1, ?_⟩
        rw [ha, one_smul] at hfirst
        have hneg : -v = v := by
          ext x
          exact CharTwo.neg_eq (v x)
        exact (eq_neg_of_add_eq_zero_left hfirst).trans hneg
    refine ⟨⟨z.val.1, ?_⟩, ?_⟩
    · rw [ha, zero_smul, add_zero] at hfirst
      exact hfirst
    · exact hsecond
  let g : LinearMap.ker (v.comp (LinearMap.ker C).subtype) →
      LinearMap.ker (borderedPolarMap C v) := fun x ↦ by
    refine ⟨(x.val.val, 0), ?_⟩
    apply Prod.ext
    · simpa using x.val.property
    · exact x.property
  exact
    { toFun := f
      invFun := g
      left_inv := fun z ↦ by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hz := z.property
          have hfirst := congrArg Prod.fst hz
          change C z.val.1 + z.val.2 • v = 0 at hfirst
          rcases binary_eq_zero_or_one z.val.2 with ha | ha
          · exact ha.symm
          · exfalso
            apply hv
            refine ⟨z.val.1, ?_⟩
            rw [ha, one_smul] at hfirst
            have hneg : -v = v := by
              ext x
              exact CharTwo.neg_eq (v x)
            exact (eq_neg_of_add_eq_zero_left hfirst).trans hneg
      right_inv := fun x ↦ Subtype.ext (Subtype.ext rfl) }

/-- If the bordering functional is outside the old range, the bordered map
has rank two larger. -/
theorem borderedPolarMap_rank_of_not_mem_range
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hsym : ∀ x y, C x y = C y x) (v : Module.Dual (ZMod 2) V)
    (hv : v ∉ LinearMap.range C) :
    Module.finrank (ZMod 2) (LinearMap.range (borderedPolarMap C v)) =
      Module.finrank (ZMod 2) (LinearMap.range C) + 2 := by
  let K := LinearMap.ker C
  let w : Module.Dual (ZMod 2) K := v.comp K.subtype
  have hw : w ≠ 0 := by
    intro hz
    apply hv
    apply mem_range_of_forall_mem_ker_eq_zero C hsym v
    intro x hx
    have he := LinearMap.congr_fun hz ⟨x, hx⟩
    exact he
  have hkerw := Module.Dual.finrank_ker_add_one_of_ne_zero hw
  have hequiv := borderedKernelEquiv_of_not_mem_range C v hv
  have hkercard := Nat.card_congr hequiv
  have hkerfin : Module.finrank (ZMod 2) (LinearMap.ker (borderedPolarMap C v)) =
      Module.finrank (ZMod 2) (LinearMap.ker w) := by
    have hc₁ := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.ker (borderedPolarMap C v))
    have hc₂ := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker w)
    rw [show Nat.card (ZMod 2) = 2 by rw [Nat.card_eq_fintype_card, ZMod.card]] at hc₁ hc₂
    rw [hc₁, hc₂] at hkercard
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hkercard
  have hC := C.finrank_range_add_finrank_ker
  have hB := (borderedPolarMap C v).finrank_range_add_finrank_ker
  have hprod : Module.finrank (ZMod 2) (V × ZMod 2) =
      Module.finrank (ZMod 2) V + 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  rw [hprod, hkerfin] at hB
  change Module.finrank (ZMod 2) (LinearMap.ker w) + 1 =
    Module.finrank (ZMod 2) (LinearMap.ker C) at hkerw
  omega

/-- When the bordering functional is in the old range, the bordered kernel
is the product of the old kernel with the new scalar coordinate. -/
noncomputable def borderedKernelEquiv_of_mem_range
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hsym : ∀ x y, C x y = C y x) (halt : ∀ x, C x x = 0)
    (v : Module.Dual (ZMod 2) V) (hv : v ∈ LinearMap.range C) :
    LinearMap.ker (borderedPolarMap C v) ≃ (LinearMap.ker C × ZMod 2) := by
  let y := Classical.choose hv
  have hy : C y = v := Classical.choose_spec hv
  let f : LinearMap.ker (borderedPolarMap C v) → LinearMap.ker C × ZMod 2 := fun z ↦ by
    have hz := z.property
    have hfirst := congrArg Prod.fst hz
    change C z.val.1 + z.val.2 • v = 0 at hfirst
    refine (⟨z.val.1 + z.val.2 • y, ?_⟩, z.val.2)
    change C (z.val.1 + z.val.2 • y) = 0
    rw [map_add, map_smul, hy]
    exact hfirst
  let g : LinearMap.ker C × ZMod 2 → LinearMap.ker (borderedPolarMap C v) := fun z ↦ by
    refine ⟨(z.1.val + z.2 • y, z.2), ?_⟩
    apply Prod.ext
    · change C (z.1.val + z.2 • y) + z.2 • v = 0
      rw [map_add, map_smul, z.1.property, zero_add, hy, ← add_smul,
        CharTwo.add_self_eq_zero, zero_smul]
    · change v (z.1.val + z.2 • y) = 0
      rw [map_add, map_smul, ← hy, hsym y z.1.val, z.1.property]
      simp [halt]
  exact
    { toFun := f
      invFun := g
      left_inv := fun z ↦ by
        apply Subtype.ext
        apply Prod.ext
        · change (z.val.1 + z.val.2 • y) + z.val.2 • y = z.val.1
          rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
        · rfl
      right_inv := fun z ↦ by
        apply Prod.ext
        · apply Subtype.ext
          change (z.1.val + z.2 • y) + z.2 • y = z.1.val
          rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
        · rfl }

/-- If the bordering functional is in the old range, bordering does not
change the rank of a symmetric alternating binary form. -/
theorem borderedPolarMap_rank_of_mem_range
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hsym : ∀ x y, C x y = C y x) (halt : ∀ x, C x x = 0)
    (v : Module.Dual (ZMod 2) V) (hv : v ∈ LinearMap.range C) :
    Module.finrank (ZMod 2) (LinearMap.range (borderedPolarMap C v)) =
      Module.finrank (ZMod 2) (LinearMap.range C) := by
  have hequiv := borderedKernelEquiv_of_mem_range C hsym halt v hv
  have hkercard := Nat.card_congr hequiv
  have hkerfin : Module.finrank (ZMod 2) (LinearMap.ker (borderedPolarMap C v)) =
      Module.finrank (ZMod 2) (LinearMap.ker C) + 1 := by
    have hc₁ := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.ker (borderedPolarMap C v))
    rw [show Nat.card (ZMod 2) = 2 by rw [Nat.card_eq_fintype_card, ZMod.card]] at hc₁
    have hprod : Nat.card (LinearMap.ker C × ZMod 2) =
        2 ^ (Module.finrank (ZMod 2) (LinearMap.ker C) + 1) := by
      rw [Nat.card_prod, Module.natCard_eq_pow_finrank (K := ZMod 2),
        show Nat.card (ZMod 2) = 2 by rw [Nat.card_eq_fintype_card, ZMod.card], pow_add]
      simp
    rw [hc₁, hprod] at hkercard
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hkercard
  have hC := C.finrank_range_add_finrank_ker
  have hB := (borderedPolarMap C v).finrank_range_add_finrank_ker
  have hprod : Module.finrank (ZMod 2) (V × ZMod 2) =
      Module.finrank (ZMod 2) V + 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  rw [hprod, hkerfin] at hB
  omega

/-- Complete two-case rank update for bordering a symmetric alternating
binary form. -/
theorem borderedPolarMap_rank_cases
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hsym : ∀ x y, C x y = C y x) (halt : ∀ x, C x x = 0)
    (v : Module.Dual (ZMod 2) V) :
    (v ∈ LinearMap.range C →
      Module.finrank (ZMod 2) (LinearMap.range (borderedPolarMap C v)) =
        Module.finrank (ZMod 2) (LinearMap.range C)) ∧
    (v ∉ LinearMap.range C →
      Module.finrank (ZMod 2) (LinearMap.range (borderedPolarMap C v)) =
        Module.finrank (ZMod 2) (LinearMap.range C) + 2) := by
  exact ⟨borderedPolarMap_rank_of_mem_range C hsym halt v,
    borderedPolarMap_rank_of_not_mem_range C hsym v⟩


open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The map to the dual whose matrix in a basis and its dual is `C`. -/
noncomputable def matrixPolarMap (C : Matrix n n (ZMod 2)) :
    (n → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (n → ZMod 2) :=
  Matrix.toLin (Pi.basisFun (ZMod 2) n) (Pi.basisFun (ZMod 2) n).dualBasis C

/-- The functional having coordinate row `v` in the standard basis. -/
noncomputable def matrixVectorDual (v : n → ZMod 2) :
    Module.Dual (ZMod 2) (n → ZMod 2) :=
  (Pi.basisFun (ZMod 2) n).dualBasis.equivFun.symm v

/-- A symmetric one-coordinate border around a square matrix. -/
def borderedAlternatingMatrix (C : Matrix n n (ZMod 2)) (v : n → ZMod 2) :
    Matrix (n ⊕ Unit) (n ⊕ Unit) (ZMod 2) :=
  Matrix.fromBlocks C (fun i _ ↦ v i) (fun _ j ↦ v j) 0

@[simp] theorem matrixVectorDual_apply_basis (v : n → ZMod 2) (i : n) :
    matrixVectorDual v (Pi.basisFun (ZMod 2) n i) = v i := by
  rw [← Module.Basis.dualBasis_repr, ← Module.Basis.equivFun_apply,
    matrixVectorDual, LinearEquiv.apply_symm_apply]


theorem matrixPolarMap_apply (C : Matrix n n (ZMod 2)) (x y : n → ZMod 2) :
    matrixPolarMap C x y = y ⬝ᵥ (C *ᵥ x) := by
  rw [matrixPolarMap, Matrix.toLin_apply]
  simp
  have hr : ⇑((Pi.basisFun (ZMod 2) n).repr x) = x :=
    funext (Pi.basisFun_repr (ZMod 2) n x)
  rw [hr]
  exact dotProduct_comm _ _

@[simp] theorem matrixPolarMap_apply_basis (C : Matrix n n (ZMod 2)) (j i : n) :
    matrixPolarMap C (Pi.basisFun (ZMod 2) n j) (Pi.basisFun (ZMod 2) n i) = C i j := by
  have h := congrFun (congrFun
    (LinearMap.toMatrix_toLin (Pi.basisFun (ZMod 2) n)
      (Pi.basisFun (ZMod 2) n).dualBasis C) i) j
  simpa [matrixPolarMap, LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr] using h


/-- Coordinates of the dual-valued map are ordinary matrix-vector multiplication. -/
theorem matrixPolarMap_equivFun (C : Matrix n n (ZMod 2)) (x : n → ZMod 2) :
    (Pi.basisFun (ZMod 2) n).dualBasis.equivFun (matrixPolarMap C x) = C *ᵥ x := by
  rw [Module.Basis.equivFun_apply]
  have h := Matrix.repr_toLin (Pi.basisFun (ZMod 2) n)
    (Pi.basisFun (ZMod 2) n).dualBasis C x
  rw [← matrixPolarMap] at h
  ext i
  exact congrFun h i

/-- Membership in the intrinsic range is ordinary column-space membership. -/
theorem matrixVectorDual_mem_range_iff (C : Matrix n n (ZMod 2)) (v : n → ZMod 2) :
    matrixVectorDual v ∈ LinearMap.range (matrixPolarMap C) ↔
      v ∈ LinearMap.range (Matrix.toLin' C) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have h := congrArg (Pi.basisFun (ZMod 2) n).dualBasis.equivFun hx
    rw [matrixPolarMap_equivFun, matrixVectorDual,
      LinearEquiv.apply_symm_apply] at h
    simpa [Matrix.toLin'_apply] using h
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply (Pi.basisFun (ZMod 2) n).dualBasis.equivFun.injective
    rw [matrixPolarMap_equivFun, matrixVectorDual, LinearEquiv.apply_symm_apply]
    simpa [Matrix.toLin'_apply] using hx


/-- The block matrix is the matrix of the abstract bordered polar map. -/
theorem borderedAlternatingMatrix_eq_toMatrix
    (C : Matrix n n (ZMod 2)) (v : n → ZMod 2) :
    borderedAlternatingMatrix C v =
      LinearMap.toMatrix
        ((Pi.basisFun (ZMod 2) n).prod (Module.Basis.singleton Unit (ZMod 2)))
        ((Pi.basisFun (ZMod 2) n).dualBasis.prod (Module.Basis.singleton Unit (ZMod 2)))
        (borderedPolarMap (matrixPolarMap C) (matrixVectorDual v)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change C i j = _
    simpa [LinearMap.toMatrix_apply, Module.Basis.prod_apply,
      Module.Basis.dualBasis_repr] using (matrixPolarMap_apply_basis C j i).symm
  · change v i = _
    simpa [LinearMap.toMatrix_apply, Module.Basis.prod_apply,
      Module.Basis.dualBasis_repr] using (matrixVectorDual_apply_basis v i).symm
  · change v j = _
    simpa [LinearMap.toMatrix_apply, Module.Basis.prod_apply]
      using (matrixVectorDual_apply_basis v j).symm
  · change (0 : ZMod 2) = _
    simp [LinearMap.toMatrix_apply, Module.Basis.prod_apply]


/-- Matrix rank equals the intrinsic rank of its associated map to the dual. -/
theorem matrix_rank_eq_matrixPolarMap_finrank (C : Matrix n n (ZMod 2)) :
    C.rank = Module.finrank (ZMod 2) (LinearMap.range (matrixPolarMap C)) := by
  exact Matrix.rank_eq_finrank_range_toLin C
    (Pi.basisFun (ZMod 2) n).dualBasis (Pi.basisFun (ZMod 2) n)

/-- The bordered matrix has the same rank as the abstract bordered map. -/
theorem borderedAlternatingMatrix_rank_eq (C : Matrix n n (ZMod 2)) (v : n → ZMod 2) :
    (borderedAlternatingMatrix C v).rank =
      Module.finrank (ZMod 2)
        (LinearMap.range (borderedPolarMap (matrixPolarMap C) (matrixVectorDual v))) := by
  rw [borderedAlternatingMatrix_eq_toMatrix]
  rw [Matrix.rank_eq_finrank_range_toLin _
    ((Pi.basisFun (ZMod 2) n).dualBasis.prod (Module.Basis.singleton Unit (ZMod 2)))
    ((Pi.basisFun (ZMod 2) n).prod (Module.Basis.singleton Unit (ZMod 2)))]
  rw [Matrix.toLin_toMatrix]

/-- A symmetric block border has unchanged rank in the old range and rank two
larger outside it. -/
theorem borderedAlternatingMatrix_rank_cases
    (C : Matrix n n (ZMod 2))
    (hsym : ∀ i j, C i j = C j i)
    (halt : ∀ x : n → ZMod 2, x ⬝ᵥ (C *ᵥ x) = 0)
    (v : n → ZMod 2) :
    ((v ∈ LinearMap.range (Matrix.toLin' C) ∧
        (borderedAlternatingMatrix C v).rank = C.rank) ∨
      (v ∉ LinearMap.range (Matrix.toLin' C) ∧
        (borderedAlternatingMatrix C v).rank = C.rank + 2)) := by
  have hC : C.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    exact hsym j i
  have hsym' : ∀ x y, matrixPolarMap C x y = matrixPolarMap C y x := by
    intro x y
    rw [matrixPolarMap_apply, matrixPolarMap_apply]
    exact hC.dotProduct_mulVec_comm
  have halt' : ∀ x, matrixPolarMap C x x = 0 := by
    intro x
    rw [matrixPolarMap_apply]
    exact halt x
  obtain ⟨hin, hout⟩ :=
    borderedPolarMap_rank_cases (matrixPolarMap C) hsym' halt' (matrixVectorDual v)
  by_cases hv : v ∈ LinearMap.range (Matrix.toLin' C)
  · left
    refine ⟨hv, ?_⟩
    rw [borderedAlternatingMatrix_rank_eq, matrix_rank_eq_matrixPolarMap_finrank]
    exact hin ((matrixVectorDual_mem_range_iff C v).2 hv)
  · right
    refine ⟨hv, ?_⟩
    rw [borderedAlternatingMatrix_rank_eq, matrix_rank_eq_matrixPolarMap_finrank]
    exact hout (by simpa [matrixVectorDual_mem_range_iff C v] using hv)


end BinaryFieldCounterexamples.Gold
