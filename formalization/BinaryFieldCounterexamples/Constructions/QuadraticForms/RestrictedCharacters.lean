/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.Coordinates
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
/-!
# Actual restricted quadratic/symmetric character orthogonality

Symmetric matrices supported on a subspace are spanned by its rank-one
matrices, over every field. A projection proves the support-restricted
spanning statement. Consequently their pairing annihilator is exactly
quadratic vanishing on that subspace. Matrices whose kernel contains U are
supported on its standard-dot annihilator, giving the literal restricted
character identity without association-scheme eigenvalue assumptions.

The resulting incidence identity does not by itself establish Schmidt's
rank/type-weighted moments; that further enumeration remains separate.
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

/-- A diagonal symmetric coordinate is the corresponding rank-one unit matrix. -/
theorem symmetric_single_diag (d : ℕ) (i : Fin d) :
    symmetricOfUpper (k:=k) d (Pi.single ⟨(i,i),le_rfl⟩ 1)=rankOneMatrix d (unitVector d i) := by
  apply (symmetricUpperEquiv d).injective
  change symmetricUpper d _ = symmetricUpper d _
  rw [symmetricUpper_ofUpper]
  funext p
  have he : (⟨(i,i),le_rfl⟩ : UpperIndex d)=p ↔ i=p.val.1 ∧ i=p.val.2 := by
    constructor
    · intro h; cases h; simp
    · rintro ⟨h1,h2⟩; exact Subtype.ext (Prod.ext h1 h2)
  simp only [Pi.single_apply,symmetricUpper,rankOneMatrix,unitVector,LinearMap.coe_mk,
    AddHom.coe_mk]
  split_ifs <;> simp_all

/-- A strict-upper symmetric coordinate is a sum of three actual rank-one matrices. -/
theorem symmetric_single_offDiag (d : ℕ) (i j : Fin d) (hij : i < j) :
    symmetricOfUpper (k:=k) d (Pi.single ⟨(i,j),hij.le⟩ 1)=
      rankOneMatrix d (unitVector d i+unitVector d j)-
        rankOneMatrix d (unitVector d i)-rankOneMatrix d (unitVector d j) := by
  apply (symmetricUpperEquiv d).injective
  change symmetricUpper d _ = symmetricUpper d _
  rw [symmetricUpper_ofUpper]
  funext p
  have hp := p.property
  have he : (⟨(i,j),hij.le⟩ : UpperIndex d)=p ↔ i=p.val.1 ∧ j=p.val.2 := by
    constructor
    · intro h; cases h; simp
    · rintro ⟨h1,h2⟩; exact Subtype.ext (Prod.ext h1 h2)
  simp only [map_sub,Pi.sub_apply,Pi.single_apply,symmetricUpper,rankOneMatrix,unitVector,
    LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply]
  split_ifs <;> simp_all
  all_goals omega

/-- Actual symmetric matrices are spanned by rank-one matrices over every field. -/
theorem span_rankOne_eq_top (d : ℕ) :
    Submodule.span k (Set.range (rankOneMatrix (k:=k) d)) = ⊤ := by
  apply top_unique
  intro M hM
  have hone (p : UpperIndex d) : symmetricOfUpper (k:=k) d (Pi.single p 1) ∈
      Submodule.span k (Set.range (rankOneMatrix (k:=k) d)) := by
    have hmem (x : Fin d → k) : rankOneMatrix d x ∈
        Submodule.span k (Set.range (rankOneMatrix (k:=k) d)) :=
      Submodule.subset_span ⟨x,rfl⟩
    obtain ⟨⟨i,j⟩,hp⟩ := p
    by_cases h : i=j
    ·
      subst j
      rw [symmetric_single_diag]
      exact hmem _
    · have hlt := lt_of_le_of_ne hp h
      rw [symmetric_single_offDiag d i j hlt]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (hmem _) (hmem _)) (hmem _)
  have he : symmetricUpper d M = ∑ p : UpperIndex d, (symmetricUpper d M p) • Pi.single p 1 := by
    funext q
    simp [Pi.single_apply]
  rw [← symmetricOfUpper_upper d M,he,map_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hone p)
/-- Actual congruence of symmetric matrices is a scalar-linear operation. -/
noncomputable def symmetricCongruence (d : ℕ) (P : Matrix (Fin d) (Fin d) k) :
    symmetricMatrices (k:=k) d →ₗ[k] symmetricMatrices (k:=k) d :=
  { toFun := fun M => ⟨P*M.val*P.transpose, by
      have hM : M.val.transpose=M.val := Matrix.ext (fun i j => M.property j i)
      have h : (P*M.val*P.transpose).transpose=P*M.val*P.transpose := by
        simp [Matrix.transpose_mul,hM,Matrix.mul_assoc]
      intro i j
      exact congrArg (fun A => A j i) h⟩
    map_add' := by intro M N; apply Subtype.ext; simp [Matrix.mul_add,Matrix.add_mul]
    map_smul' := by intro u M; apply Subtype.ext; simp }

/-- Congruence transports actual rank-one matrices by the corresponding vector map. -/
theorem symmetricCongruence_rankOne (d : ℕ) (P : Matrix (Fin d) (Fin d) k) (x : Fin d → k) :
    symmetricCongruence d P (rankOneMatrix d x)=rankOneMatrix d (P *ᵥ x) := by
  apply Subtype.ext
  change P * Matrix.vecMulVec x x * P.transpose = Matrix.vecMulVec (P *ᵥ x) (P *ᵥ x)
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_transpose]

/-- Symmetric matrices supported on a subspace have every literal column in that subspace. -/
def supportedMatrices (d : ℕ) (W : Submodule k (Fin d → k)) :
    Submodule k (symmetricMatrices (k:=k) d) :=
  { carrier := {M | ∀ j, (fun i => M.val i j) ∈ W}
    zero_mem' := by intro j; exact W.zero_mem
    add_mem' := by intro M N hM hN j; exact W.add_mem (hM j) (hN j)
    smul_mem' := by intro u M hM j; exact W.smul_mem u (hM j) }

/-- Rank-one matrices of vectors in the support subspace have the required column support. -/
theorem rankOne_mem_supported (d : ℕ) (W : Submodule k (Fin d → k))
    (x : Fin d → k) (hx : x ∈ W) : rankOneMatrix d x ∈ supportedMatrices d W := by
  intro j
  have h := W.smul_mem (x j) hx
  convert h using 1
  funext i
  simp [rankOneMatrix,Pi.smul_apply,smul_eq_mul,mul_comm]

/-- A projection fixing the support subspace fixes every supported symmetric matrix by congruence. -/
theorem symmetricCongruence_eq_of_supported (d : ℕ) (W : Submodule k (Fin d → k))
    (P : Matrix (Fin d) (Fin d) k) (hP : ∀ x ∈ W, P *ᵥ x=x)
    (M : symmetricMatrices (k:=k) d) (hM : M ∈ supportedMatrices d W) :
    symmetricCongruence d P M=M := by
  have hl : P*M.val=M.val := by
    ext i j
    exact congrFun (hP (fun z => M.val z j) (hM j)) i
  have hs : M.val.transpose=M.val := Matrix.ext (fun i j => M.property j i)
  have hr := congrArg Matrix.transpose hl
  simp only [Matrix.transpose_mul,hs] at hr
  apply Subtype.ext
  change P*M.val*P.transpose=M.val
  rw [hl,hr]

/-- Supported symmetric matrices are exactly spanned by rank-one matrices from the support subspace. -/
theorem span_rankOne_subspace (d : ℕ) (W : Submodule k (Fin d → k)) :
    Submodule.span k (rankOneMatrix (k:=k) d '' (W : Set (Fin d → k)))=supportedMatrices d W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro M ⟨x,hx,rfl⟩
    exact rankOne_mem_supported d W x hx
  · intro M hM
    obtain ⟨W',hcompl⟩ := W.exists_isCompl
    let E := W.projection W' hcompl
    let P := LinearMap.toMatrix' E
    have hPx (x : Fin d → k) : P *ᵥ x=E x := by
      exact LinearMap.toMatrix'_mulVec E x
    have hfix : symmetricCongruence d P M=M :=
      symmetricCongruence_eq_of_supported d W P
        (fun x hx => (hPx x).trans (W.projection_apply_of_mem_left hcompl hx)) M hM
    rw [← hfix]
    have hall : M ∈ Submodule.span k (Set.range (rankOneMatrix (k:=k) d)) := by
      rw [span_rankOne_eq_top]; trivial
    clear hM hfix
    induction hall using Submodule.span_induction with
    | mem N hN =>
      obtain ⟨x,rfl⟩ := hN
      rw [symmetricCongruence_rankOne,hPx]
      exact Submodule.subset_span ⟨E x,W.projection_apply_mem hcompl x,rfl⟩
    | zero => simp
    | add A B hA hB ihA ihB =>
      rw [map_add]
      exact Submodule.add_mem _ ihA ihB
    | smul u A hA ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ u ih
/-- Pairing annihilation on the actual supported matrix subspace is exactly quadratic vanishing there. -/
theorem pairing_supported_iff (d : ℕ) (W : Submodule k (Fin d → k))
    (Q : QuadraticForm k (Fin d → k)) :
    (∀ M ∈ supportedMatrices d W, matrixPairing d Q M=0) ↔ ∀ x ∈ W, Q x=0 := by
  constructor
  · intro h x hx
    simpa only [matrixPairing_rankOne] using h (rankOneMatrix d x) (rankOne_mem_supported d W x hx)
  · intro h M hM
    have hs : Submodule.span k (rankOneMatrix (k:=k) d '' (W : Set (Fin d → k))) ≤
        (matrixPairingLinear d Q).ker := by
      apply Submodule.span_le.mpr
      rintro N ⟨x,hx,rfl⟩
      change matrixPairing d Q (rankOneMatrix d x)=0
      rw [matrixPairing_rankOne]
      exact h x hx
    rw [span_rankOne_subspace] at hs
    exact hs hM

/-- The literal annihilator under the standard coordinate dot pairing. -/
def dotAnnihilator (d : ℕ) (U : Submodule k (Fin d → k)) : Submodule k (Fin d → k) :=
  { carrier := {x | ∀ u ∈ U, x ⬝ᵥ u=0}
    zero_mem' := by simp
    add_mem' := by intro x y hx hy u hu; rw [add_dotProduct,hx u hu,hy u hu,add_zero]
    smul_mem' := by intro a x hx u hu; rw [smul_dotProduct,hx u hu,smul_zero] }

/-- Supported matrices on the dot annihilator are exactly symmetric matrices with the prescribed kernel. -/
theorem mem_supported_dotAnnihilator_iff (d : ℕ) (U : Submodule k (Fin d → k))
    (M : symmetricMatrices (k:=k) d) :
    M ∈ supportedMatrices d (dotAnnihilator d U) ↔ ∀ u ∈ U, M.val *ᵥ u=0 := by
  have hcol (j : Fin d) : (fun i => M.val i j)=(fun i => M.val j i) :=
    funext (fun i => M.property i j)
  constructor
  · intro h u hu
    funext j
    have hj := h j u hu
    rw [hcol] at hj
    exact hj
  · intro h j u hu
    rw [hcol]
    exact congrFun (h u hu) j

/-- The annihilator of matrices whose radical contains U is quadratic vanishing on U's dot annihilator. -/
theorem pairing_kernel_containing_iff (d : ℕ) (U : Submodule k (Fin d → k))
    (Q : QuadraticForm k (Fin d → k)) :
    (∀ M : symmetricMatrices (k:=k) d, (∀ u ∈ U, M.val *ᵥ u=0) → matrixPairing d Q M=0) ↔
      ∀ x ∈ dotAnnihilator d U, Q x=0 := by
  simpa only [mem_supported_dotAnnihilator_iff] using pairing_supported_iff d (dotAnnihilator d U) Q
/-- A nonzero scalar-linear functional preserves nontriviality of an additive character. -/
theorem character_comp_linear_ne_one {V R : Type*} [AddCommGroup V] [Module k V]
    [CommRing R] (ψ : AddChar k R) (hψ : ψ≠1) (L : V →ₗ[k] k) (hL : L≠0) :
    ψ.compAddMonoidHom L.toAddMonoidHom ≠ 1 := by
  obtain ⟨b,hb⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨x,hx⟩ : ∃ x, L x≠0 := by
    by_contra h
    apply hL
    ext x
    simpa using not_exists.mp h x
  apply AddChar.ne_one_iff.mpr
  refine ⟨(b/(L x)) • x, ?_⟩
  simpa only [AddChar.compAddMonoidHom_apply,LinearMap.toAddMonoidHom_coe,map_smul,
    smul_eq_mul,div_mul_cancel₀ _ hx] using hb

/-- Finite scalar-linear character orthogonality, with a nontrivial character of the full field. -/
theorem sum_character_linear {V R : Type*} [AddCommGroup V] [Module k V] [Fintype V]
    [CommRing R] [IsDomain R] (ψ : AddChar k R) (hψ : ψ≠1) (L : V →ₗ[k] k) :
    ∑ x : V, ψ (L x) = if L=0 then (Fintype.card V : R) else 0 := by
  by_cases hL : L=0
  · simp [hL]
  · rw [ite_eq_right hL]
    exact AddChar.sum_eq_zero_of_ne_one (character_comp_linear_ne_one ψ hψ L hL)

/-- Restrict the actual quadratic/symmetric pairing to any concrete symmetric-matrix submodule. -/
noncomputable def restrictedMatrixFunctional (d : ℕ)
    (S : Submodule k (symmetricMatrices (k:=k) d))
    (Q : QuadraticForm k (Fin d → k)) : S →ₗ[k] k :=
  (matrixPairingLinear d Q).comp S.subtype

/-- The exact character sum on any actual symmetric-matrix submodule. -/
theorem sum_character_symmetric_submodule {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ) (S : Submodule k (symmetricMatrices (k:=k) d)) [Fintype S]
    (ψ : AddChar k R) (hψ : ψ≠1) (Q : QuadraticForm k (Fin d → k)) :
    ∑ M : S, ψ (matrixPairing d Q M.val) =
      if (∀ M ∈ S, matrixPairing d Q M=0) then (Fintype.card S : R) else 0 := by
  have he : restrictedMatrixFunctional d S Q=0 ↔ ∀ M ∈ S, matrixPairing d Q M=0 := by
    simp only [LinearMap.ext_iff,restrictedMatrixFunctional,LinearMap.coe_comp,
      Function.comp_apply,Submodule.coe_subtype,LinearMap.zero_apply]
    exact Subtype.forall
  convert sum_character_linear (V:=S) ψ hψ (restrictedMatrixFunctional d S Q) using 1
  · rfl
  · simp only [he]
/-- Exact character orthogonality for symmetric matrices supported on any actual subspace. -/
theorem sum_character_supported_matrices [Fintype k] {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ) (W : Submodule k (Fin d → k)) (ψ : AddChar k R) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d → k)) :
    ∑ M : supportedMatrices d W, ψ (matrixPairing d Q M.val) =
      if (∀ x ∈ W, Q x=0) then (Fintype.card (supportedMatrices d W) : R) else 0 := by
  rw [sum_character_symmetric_submodule d (supportedMatrices d W) ψ hψ Q]
  simp only [pairing_supported_iff]

/-- Exact character sum for symmetric matrices with a prescribed subspace in their radical. -/
theorem sum_character_kernel_containing [Fintype k] {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ) (U : Submodule k (Fin d → k)) (ψ : AddChar k R) (hψ : ψ≠1)
    (Q : QuadraticForm k (Fin d → k)) :
    ∑ M : supportedMatrices d (dotAnnihilator d U), ψ (matrixPairing d Q M.val) =
      if (∀ x ∈ dotAnnihilator d U, Q x=0)
      then (Fintype.card (supportedMatrices d (dotAnnihilator d U)) : R) else 0 := by
  exact sum_character_supported_matrices d (dotAnnihilator d U) ψ hψ Q
end BinaryFieldCounterexamples.QuadraticCoordinates
