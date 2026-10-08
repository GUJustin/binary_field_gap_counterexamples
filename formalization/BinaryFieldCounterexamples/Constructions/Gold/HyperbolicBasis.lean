/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicSplit
public import BinaryFieldCounterexamples.Constructions.Gold.HyperbolicAugment
public import Mathlib.LinearAlgebra.Basis.Fin
public import BinaryFieldCounterexamples.Constructions.Gold.AlternatingCoordinates
/-!
# A basis adapted to a hyperbolic splitting

The orthogonal-complement basis followed by the two hyperbolic vectors gives
an explicit basis of the original space. Its literal upper-coordinate tensor
is exactly the canonical hyperbolic augmentation of the restricted tensor.
The tensor matrix and rank agree with the actual bilinear map in each basis.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Append the two hyperbolic vectors to the orthogonal-complement basis. -/
noncomputable def hyperbolicSplitBasis
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1)
    {d : ℕ} (e : Module.Basis (Fin d) (ZMod 2) (hyperbolicComplement C x y)) :
    Module.Basis (Fin (d+2)) (ZMod 2) V :=
  ((e.prod (Module.Basis.finTwoProd (ZMod 2))).map
    (hyperbolicSplitEquiv C x y hs ha hxy).symm).reindex finSumFinEquiv

/-- Old basis vectors are included literally. -/
theorem hyperbolicSplitBasis_old
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1)
    {d : ℕ} (e : Module.Basis (Fin d) (ZMod 2) (hyperbolicComplement C x y)) (i : Fin d) :
    hyperbolicSplitBasis C x y hs ha hxy e (Fin.castAdd 2 i)=(e i : V) := by
  simp [hyperbolicSplitBasis,Module.Basis.reindex_apply,finSumFinEquiv_symm_apply_castAdd,
    Module.Basis.prod_apply,hyperbolicSplitEquiv]

/-- The first new basis vector is the chosen x. -/
theorem hyperbolicSplitBasis_x
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1)
    {d : ℕ} (e : Module.Basis (Fin d) (ZMod 2) (hyperbolicComplement C x y)) :
    hyperbolicSplitBasis C x y hs ha hxy e (Fin.natAdd d 0)=x := by
  simp [hyperbolicSplitBasis,Module.Basis.reindex_apply,finSumFinEquiv_symm_apply_natAdd,
    Module.Basis.prod_apply,hyperbolicSplitEquiv,Module.Basis.finTwoProd_zero]

/-- The final basis vector is the chosen y. -/
theorem hyperbolicSplitBasis_y
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1)
    {d : ℕ} (e : Module.Basis (Fin d) (ZMod 2) (hyperbolicComplement C x y)) :
    hyperbolicSplitBasis C x y hs ha hxy e (Fin.natAdd d 1)=y := by
  simp [hyperbolicSplitBasis,Module.Basis.reindex_apply,finSumFinEquiv_symm_apply_natAdd,
    Module.Basis.prod_apply,hyperbolicSplitEquiv,Module.Basis.finTwoProd_one]
/-- The actual upper-triangular pairing values of a form in a basis. -/
noncomputable def basisTensor
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) V) : TensorIndex d → ZMod 2 :=
  fun ij => C (e ij.val.1) (e ij.val.2)

/-- The tensor matrix is the actual matrix of the form in the basis and dual basis. -/
theorem basisTensor_matrix
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) V) :
    tensorAlternatingMatrix (basisTensor C e) = LinearMap.toMatrix e e.dualBasis C := by
  ext i j
  rw [LinearMap.toMatrix_apply,e.dualBasis_repr]
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [tensorAlternatingMatrix_apply_lt (basisTensor C e) hij]
    exact hs _ _
  · rw [tensorAlternatingMatrix_diagonal,ha]
  · have hh := congrFun (congrFun (tensorAlternatingMatrix_transpose (basisTensor C e)) i) j
    rw [← hh,Matrix.transpose_apply,tensorAlternatingMatrix_apply_lt (basisTensor C e) hji]
    rfl

/-- Coordinate tensor rank equals the intrinsic rank of the form. -/
theorem basisTensor_rank
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) {d : ℕ}
    (e : Module.Basis (Fin d) (ZMod 2) V) :
    (tensorAlternatingMatrix (basisTensor C e)).rank =
      Module.finrank (ZMod 2) (LinearMap.range C) := by
  rw [basisTensor_matrix C hs ha e]
  have h := Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix e e.dualBasis C) e.dualBasis e
  rw [Matrix.toLin_toMatrix] at h
  exact h
/-- The adapted basis produces precisely one canonical hyperbolic augmentation. -/
theorem basisTensor_hyperbolicSplitBasis
    (C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (x y : V)
    (hs : ∀ a b, C a b=C b a) (ha : ∀ a, C a a=0) (hxy : C x y=1)
    {d : ℕ} (e : Module.Basis (Fin d) (ZMod 2) (hyperbolicComplement C x y)) :
    basisTensor C (hyperbolicSplitBasis C x y hs ha hxy e) =
      hyperbolicAugment d (basisTensor (hyperbolicRestrictedMap C x y) e) := by
  let e' := hyperbolicSplitBasis C x y hs ha hxy e
  have hold (i : Fin d) : e' i.castSucc.castSucc=(e i : V) :=
    hyperbolicSplitBasis_old C x y hs ha hxy e i
  have hx : e' (Fin.last d).castSucc=x :=
    hyperbolicSplitBasis_x C x y hs ha hxy e
  have hy : e' (Fin.last (d+1))=y :=
    hyperbolicSplitBasis_y C x y hs ha hxy e
  apply (tensorBorderEquiv (d+1)).injective
  rw [tensorBorderEquiv_hyperbolicAugment]
  apply Prod.ext
  · apply (tensorBorderEquiv d).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · funext ij
      change C (e' ij.val.1.castSucc.castSucc) (e' ij.val.2.castSucc.castSucc) =
        hyperbolicRestrictedMap C x y (e ij.val.1) (e ij.val.2)
      rw [hold,hold]
      rfl
    · funext i
      change C (e' i.castSucc.castSucc) (e' (Fin.last d).castSucc)=0
      rw [hold,hx,hs]
      exact (e i).property.1
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change C (e' (Fin.last d).castSucc) (e' (Fin.last (d+1))) = _
      rw [hx,hy,hxy]
      simp
    · change C (e' j.castSucc.castSucc) (e' (Fin.last (d+1))) = _
      rw [hold,hy,hs]
      rw [show C y (e j : V)=0 from (e j).property.2]
      simp
end BinaryFieldCounterexamples.Gold
