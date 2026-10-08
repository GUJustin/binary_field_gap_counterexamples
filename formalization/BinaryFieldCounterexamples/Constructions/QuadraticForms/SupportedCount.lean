/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RestrictedCharacters
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Sym.Card
/-!
# Exact supported-matrix cardinalities and isotropic incidence sums

Rectangular congruence by a basis inclusion is injective and its range is
exactly the actual supported symmetric-matrix subspace. The upper-coordinate
count therefore gives dimension r(r+1)/2 and the corresponding finite-field
cardinality. Summing the proved restricted character identity gives an actual
isotropic-subspace incidence identity, both as a nested sum and as a character
sum weighted by support containment. No rank/type enumeration or q-squared
association-scheme eigenvalue is assumed.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open Module Matrix
attribute [local instance] Classical.decEq Classical.propDecidable upperIndexFintype
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {k : Type*} [Field k]

/-- The actual number of upper-triangular coefficients, including the diagonal. -/
theorem upperIndex_card (d : ℕ) : Fintype.card (UpperIndex d)=d*(d+1)/2 := by
  have he : Sym2 (Fin d) ≃ UpperIndex d := Sym2.sortEquiv
  rw [← Fintype.card_congr he,Sym2.card,Fintype.card_fin,Nat.choose_two_right]
  simp [Nat.mul_comm]

/-- Actual symmetric matrices have the expected all-characteristic dimension. -/
theorem symmetricMatrices_finrank (d : ℕ) :
    Module.finrank k (symmetricMatrices (k:=k) d)=d*(d+1)/2 := by
  rw [(symmetricUpperEquiv (k:=k) d).finrank_eq,Module.finrank_pi,upperIndex_card]

/-- Rectangular congruence transports symmetric matrices along a coordinate linear map. -/
noncomputable def symmetricTransport (m d : ℕ) (P : Matrix (Fin d) (Fin m) k) :
    symmetricMatrices (k:=k) m →ₗ[k] symmetricMatrices (k:=k) d :=
  { toFun := fun M => ⟨P*M.val*P.transpose, by
      have hM : M.val.transpose=M.val := Matrix.ext (fun i j => M.property j i)
      have h : (P*M.val*P.transpose).transpose=P*M.val*P.transpose := by
        simp [Matrix.transpose_mul,hM,Matrix.mul_assoc]
      intro i j
      exact congrArg (fun A => A j i) h⟩
    map_add' := by intro M N; apply Subtype.ext; simp [Matrix.mul_add,Matrix.add_mul]
    map_smul' := by intro u M; apply Subtype.ext; simp }

/-- Rectangular congruence sends actual rank-one matrices to their vector images. -/
theorem symmetricTransport_rankOne (m d : ℕ) (P : Matrix (Fin d) (Fin m) k)
    (x : Fin m → k) :
    symmetricTransport m d P (rankOneMatrix m x)=rankOneMatrix d (P *ᵥ x) := by
  apply Subtype.ext
  change P * Matrix.vecMulVec x x * P.transpose = Matrix.vecMulVec (P *ᵥ x) (P *ᵥ x)
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_transpose]

/-- The image of rectangular congruence is exactly the matrices supported on its vector image. -/
theorem symmetricTransport_range (m d : ℕ) (E : (Fin m → k) →ₗ[k] (Fin d → k)) :
    (symmetricTransport m d (LinearMap.toMatrix' E)).range=supportedMatrices d E.range := by
  apply le_antisymm
  · rintro M ⟨N,rfl⟩
    have hN : N ∈ Submodule.span k (Set.range (rankOneMatrix (k:=k) m)) := by
      rw [span_rankOne_eq_top]; trivial
    induction hN using Submodule.span_induction with
    | mem N h =>
      obtain ⟨x,rfl⟩ := h
      rw [symmetricTransport_rankOne,LinearMap.toMatrix'_mulVec]
      exact rankOne_mem_supported d E.range (E x) ⟨x,rfl⟩
    | zero => simp
    | add A B hA hB ihA ihB =>
      rw [map_add]
      exact Submodule.add_mem _ ihA ihB
    | smul a A hA ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ a ih
  · rw [← span_rankOne_subspace]
    apply Submodule.span_le.mpr
    rintro M ⟨x,⟨v,hv⟩,rfl⟩
    refine ⟨rankOneMatrix m v,?_⟩
    rw [symmetricTransport_rankOne,LinearMap.toMatrix'_mulVec,hv]

/-- A left inverse on coordinate vectors is also a left inverse on symmetric matrices. -/
theorem symmetricTransport_leftInverse (m d : ℕ)
    (E : (Fin m → k) →ₗ[k] (Fin d → k)) (R : (Fin d → k) →ₗ[k] (Fin m → k))
    (h : R.comp E=LinearMap.id) :
    Function.LeftInverse (symmetricTransport d m (LinearMap.toMatrix' R))
      (symmetricTransport m d (LinearMap.toMatrix' E)) := by
  have hp : LinearMap.toMatrix' R * LinearMap.toMatrix' E = 1 := by
    rw [← LinearMap.toMatrix'_comp,h,LinearMap.toMatrix'_id]
  intro M
  apply Subtype.ext
  change LinearMap.toMatrix' R*(LinearMap.toMatrix' E*M.val*(LinearMap.toMatrix' E).transpose)*
    (LinearMap.toMatrix' R).transpose=M.val
  calc
    _ = (LinearMap.toMatrix' R*LinearMap.toMatrix' E)*M.val*
        (LinearMap.toMatrix' R*LinearMap.toMatrix' E).transpose := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = M.val := by rw [hp]; simp
/-- Injective vector maps induce injective transport of actual symmetric matrices. -/
theorem symmetricTransport_injective (m d : ℕ)
    (E : (Fin m → k) →ₗ[k] (Fin d → k)) (hE : Function.Injective E) :
    Function.Injective (symmetricTransport m d (LinearMap.toMatrix' E)) := by
  obtain ⟨R,hR⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hE)
  exact (symmetricTransport_leftInverse m d E R hR).injective

/-- Matrices supported on an r-dimensional actual subspace have dimension r(r+1)/2. -/
theorem supportedMatrices_finrank (d : ℕ) (W : Submodule k (Fin d → k)) :
    Module.finrank k (supportedMatrices d W)=
      (Module.finrank k W)*(Module.finrank k W+1)/2 := by
  let e := (Module.finBasis k W).equivFun
  let E := W.subtype.comp e.symm.toLinearMap
  have hE : Function.Injective E := W.subtype_injective.comp e.symm.injective
  have hr : E.range=W := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact (e.symm v).property
    · intro hx
      refine ⟨e ⟨x,hx⟩,?_⟩
      change (e.symm (e ⟨x,hx⟩)).val=x
      rw [e.symm_apply_apply]
  rw [← hr,← symmetricTransport_range]
  rw [LinearMap.finrank_range_of_inj (symmetricTransport_injective _ _ E hE),
    symmetricMatrices_finrank,hr]

/-- The exact cardinality of actual supported symmetric matrices over a finite field. -/
theorem supportedMatrices_card [Fintype k] (d : ℕ) (W : Submodule k (Fin d → k)) :
    Fintype.card (supportedMatrices d W)=
      (Fintype.card k)^((Module.finrank k W)*(Module.finrank k W+1)/2) := by
  rw [Module.card_eq_pow_finrank (K:=k),supportedMatrices_finrank]

/-- The exact restricted character sum with its explicit scalar-field cardinality factor. -/
theorem sum_character_supported_matrices_explicit [Fintype k] {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ) (W : Submodule k (Fin d → k)) (ψ : AddChar k R) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d → k)) :
    ∑ M : supportedMatrices d W, ψ (matrixPairing d Q M.val) =
      if (∀ x ∈ W, Q x=0)
      then (((Fintype.card k)^((Module.finrank k W)*(Module.finrank k W+1)/2) : ℕ) : R) else 0 := by
  rw [sum_character_supported_matrices,supportedMatrices_card]
  exact hψ
/-- Summing actual restricted character identities counts precisely the isotropic support subspaces. -/
theorem sum_character_isotropic_incidence [Fintype k] {R : Type*} [CommRing R] [IsDomain R]
    (d r : ℕ) (G : Finset (Submodule k (Fin d → k)))
    (hG : ∀ W ∈ G, Module.finrank k W=r) (ψ : AddChar k R) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ W ∈ G, ∑ M : supportedMatrices d W, ψ (matrixPairing d Q M.val)) =
      (((Fintype.card k)^(r*(r+1)/2) : ℕ) : R)*
        ((G.filter (fun W => ∀ x ∈ W, Q x=0)).card : R) := by
  calc
    _ = ∑ W ∈ G, if (∀ x ∈ W, Q x=0)
        then (((Fintype.card k)^(r*(r+1)/2) : ℕ) : R) else 0 := by
      apply Finset.sum_congr rfl
      intro W hW
      rw [sum_character_supported_matrices_explicit d W ψ hψ Q,hG W hW]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul,mul_comm]

/-- The actual finite family of subspaces of a fixed dimension. -/
noncomputable def dimensionSubspaces [Fintype k] (d r : ℕ) : Finset (Submodule k (Fin d → k)) := by
  letI : Fintype (Submodule k (Fin d → k)) := Fintype.ofFinite _
  exact Finset.univ.filter (fun W => Module.finrank k W=r)

/-- Membership in the actual fixed-dimension family is precisely its dimension equation. -/
theorem mem_dimensionSubspaces [Fintype k] (d r : ℕ) (W : Submodule k (Fin d → k)) :
    W ∈ dimensionSubspaces (k:=k) d r ↔ Module.finrank k W=r := by
  simp [dimensionSubspaces]

/-- The concrete fixed-dimension isotropic incidence identity, without assumed rank/type enumeration. -/
theorem sum_character_dimensionSubspaces [Fintype k] {R : Type*} [CommRing R] [IsDomain R]
    (d r : ℕ) (ψ : AddChar k R) (hψ : ψ≠1) (Q : QuadraticForm k (Fin d → k)) :
    (∑ W ∈ dimensionSubspaces (k:=k) d r,
      ∑ M : supportedMatrices d W, ψ (matrixPairing d Q M.val)) =
      (((Fintype.card k)^(r*(r+1)/2) : ℕ) : R)*
        (((dimensionSubspaces (k:=k) d r).filter (fun W => ∀ x ∈ W, Q x=0)).card : R) := by
  exact sum_character_isotropic_incidence d r _
    (fun W hW => (mem_dimensionSubspaces d r W).mp hW) ψ hψ Q
/-- The same actual incidence identity, regrouped as a character sum weighted by support containment. -/
theorem weighted_character_isotropic_incidence [Fintype k] {R : Type*} [CommRing R] [IsDomain R]
    (d r : ℕ) (G : Finset (Submodule k (Fin d → k)))
    (hG : ∀ W ∈ G, Module.finrank k W=r) (ψ : AddChar k R) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d → k)) :
    (∑ M : symmetricMatrices (k:=k) d,
      ((G.filter (fun W => M ∈ supportedMatrices d W)).card : R)*ψ (matrixPairing d Q M)) =
      (((Fintype.card k)^(r*(r+1)/2) : ℕ) : R)*
        ((G.filter (fun W => ∀ x ∈ W, Q x=0)).card : R) := by
  have hs (W : Submodule k (Fin d → k)) :
      (∑ M : supportedMatrices d W, ψ (matrixPairing d Q M.val)) =
        ∑ M : symmetricMatrices (k:=k) d, if M ∈ supportedMatrices d W
          then ψ (matrixPairing d Q M) else 0 := by
    simpa only [Finset.subtype_univ,Finset.sum_filter] using
      (Finset.sum_subtype_eq_sum_filter (s:=Finset.univ)
        (p:=fun M => M ∈ supportedMatrices d W) (fun M => ψ (matrixPairing d Q M)))
  calc
    _ = ∑ M : symmetricMatrices (k:=k) d, ∑ W ∈ G,
        if M ∈ supportedMatrices d W then ψ (matrixPairing d Q M) else 0 := by
      apply Finset.sum_congr rfl
      intro M hM
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul]
    _ = ∑ W ∈ G, ∑ M : symmetricMatrices (k:=k) d,
        if M ∈ supportedMatrices d W then ψ (matrixPairing d Q M) else 0 :=
      Finset.sum_comm
    _ = ∑ W ∈ G, ∑ M : supportedMatrices d W, ψ (matrixPairing d Q M.val) := by
      apply Finset.sum_congr rfl
      intro W hW
      exact (hs W).symm
    _ = _ := sum_character_isotropic_incidence d r G hG ψ hψ Q
end BinaryFieldCounterexamples.QuadraticCoordinates
