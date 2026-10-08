/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# All-characteristic quadratic coordinates and their perfect matrix pairing

Quadratic forms are reconstructed from their diagonal basis values and mixed
polar values. The inverse is the literal sum of upper-triangular monomials,
so no division by two is used. Symmetric matrices retain all diagonal entries
and pair once with each upper coefficient. Single-entry tests prove
nondegeneracy on both sides; rank-one matrices recover evaluation of the
actual quadratic form.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticCoordinates
open scoped BigOperators
open Module
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {k : Type*} [Field k]

/-- Upper-triangular indices retain both square and mixed quadratic coefficients. -/
def UpperIndex (d : ℕ) := {ij : Fin d × Fin d // ij.1 ≤ ij.2}

/-- The finite upper-triangular coefficient index set. -/
noncomputable def upperIndexFintype (d : ℕ) : Fintype (UpperIndex d) :=
  inferInstanceAs (Fintype {ij : Fin d × Fin d // ij.1 ≤ ij.2})
attribute [local instance] upperIndexFintype

/-- The coordinate unit vector. -/
def unitVector (d : ℕ) (i : Fin d) : Fin d → k := Pi.single i 1

/-- Actual diagonal values and mixed polar values as a linear coefficient map. -/
noncomputable def upperCoordinates (d : ℕ) :
    QuadraticForm k (Fin d → k) →ₗ[k] (UpperIndex d → k) :=
  {
    toFun Q p := if p.val.1=p.val.2 then Q (unitVector d p.val.1)
      else Q.polarBilin (unitVector d p.val.1) (unitVector d p.val.2)
    map_add' Q R := by
      funext p
      split_ifs with h <;> simp_all [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
      all_goals ring
    map_smul' a Q := by
      funext p
      split_ifs with h <;> simp_all [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,smul_eq_mul]
      all_goals ring
  }

/-- Build an actual quadratic form by summing its square and mixed monomials. -/
noncomputable def ofUpperCoordinates (d : ℕ) :
    (UpperIndex d → k) →ₗ[k] QuadraticForm k (Fin d → k) :=
  {
    toFun a := ∑ p : UpperIndex d, a p • QuadraticMap.proj p.val.1 p.val.2
    map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
    map_smul' u a := by simp [smul_smul,Finset.smul_sum]
  }

/-- The reconstructed form evaluates to the literal upper-triangular monomial sum. -/
theorem ofUpperCoordinates_apply (d : ℕ) (a : UpperIndex d → k) (x : Fin d → k) :
    ofUpperCoordinates d a x = ∑ p : UpperIndex d, a p*(x p.val.1*x p.val.2) := by
  simp [ofUpperCoordinates,QuadraticMap.proj_apply,smul_eq_mul]

/-- Basis values together with the full polar form determine a quadratic form in any characteristic. -/
theorem eq_of_basis_and_polar {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] (e : Basis ι k V) (Q R : QuadraticForm k V)
    (hd : ∀ i, Q (e i)=R (e i)) (hp : Q.polarBilin=R.polarBilin) : Q=R := by
  apply QuadraticMap.ext
  intro x
  rw [← e.sum_repr x,Q.map_sum,R.map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Q.map_smul,R.map_smul,hd]
  · apply Finset.sum_congr rfl
    intro p hp'
    obtain ⟨i,j⟩ := p
    simp only [Sym2.map_mk,QuadraticMap.polarSym2_sym2Mk,
      ← QuadraticMap.polarBilin_apply_apply,hp]
/-- Upper coordinates retain the diagonal quadratic values. -/
theorem upperCoordinates_diag (d : ℕ) (Q : QuadraticForm k (Fin d → k)) (i : Fin d) :
    upperCoordinates d Q ⟨(i,i),le_rfl⟩=Q (unitVector d i) := by
  simp [upperCoordinates]

/-- Strict upper coordinates are the mixed polar values. -/
theorem upperCoordinates_offDiag (d : ℕ) (Q : QuadraticForm k (Fin d → k))
    (i j : Fin d) (h : i < j) :
    upperCoordinates d Q ⟨(i,j),h.le⟩=Q.polarBilin (unitVector d i) (unitVector d j) := by
  simp [upperCoordinates,h.ne]

/-- Actual upper-triangular coordinates determine a quadratic form in every characteristic. -/
theorem upperCoordinates_injective (d : ℕ) : Function.Injective (upperCoordinates (k:=k) d) := by
  intro Q R he
  have hd (i : Fin d) : Q (unitVector d i)=R (unitVector d i) := by
    have h := congrFun he ⟨(i,i),le_rfl⟩
    simpa only [upperCoordinates_diag] using h
  have hp (i j : Fin d) : Q.polarBilin (unitVector d i) (unitVector d j)=
      R.polarBilin (unitVector d i) (unitVector d j) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · have h := congrFun he ⟨(i,j),hij.le⟩
      simpa only [upperCoordinates_offDiag d _ i j hij] using h
    · subst j
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,hd]
    · have h := congrFun he ⟨(j,i),hij.le⟩
      simpa only [upperCoordinates_offDiag d _ j i hij,
        QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm _ (unitVector d j)] using h
  apply eq_of_basis_and_polar (Pi.basisFun k (Fin d)) Q R
  · intro i
    simpa only [Pi.basisFun_apply,unitVector] using hd i
  · apply (Pi.basisFun k (Fin d)).ext
    intro i
    apply (Pi.basisFun k (Fin d)).ext
    intro j
    simpa only [LinearMap.coe_comp,Pi.basisFun_apply,unitVector] using hp i j
/-- A single upper monomial has precisely its single coefficient in every characteristic. -/
theorem upperCoordinates_proj (d : ℕ) (p q : UpperIndex d) :
    upperCoordinates d (QuadraticMap.proj (R:=k) p.val.1 p.val.2) q =
      if p=q then 1 else 0 := by
  have hp := p.property
  have hq := q.property
  have he : p=q ↔ p.val.1=q.val.1 ∧ p.val.2=q.val.2 := by
    constructor
    · rintro rfl; exact ⟨rfl,rfl⟩
    · rintro ⟨h1,h2⟩; exact Subtype.ext (Prod.ext h1 h2)
  simp only [upperCoordinates,LinearMap.coe_mk,AddHom.coe_mk,QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar,QuadraticMap.proj_apply,unitVector,Pi.add_apply,Pi.single_apply,he]
  split_ifs <;> simp_all
  all_goals omega

/-- Reconstructing from an arbitrary coefficient array returns exactly that array. -/
theorem upperCoordinates_ofUpperCoordinates (d : ℕ) (a : UpperIndex d → k) :
    upperCoordinates d (ofUpperCoordinates d a)=a := by
  funext q
  simp only [ofUpperCoordinates,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    Finset.sum_apply,Pi.smul_apply,upperCoordinates_proj,smul_eq_mul]
  simp

/-- Reconstructing an actual form's upper coordinates returns that form. -/
theorem ofUpperCoordinates_upperCoordinates (d : ℕ) (Q : QuadraticForm k (Fin d → k)) :
    ofUpperCoordinates d (upperCoordinates d Q)=Q := by
  apply upperCoordinates_injective d
  exact upperCoordinates_ofUpperCoordinates d _

/-- The actual all-characteristic linear coordinate equivalence for quadratic forms. -/
noncomputable def upperCoordinatesEquiv (d : ℕ) :
    QuadraticForm k (Fin d → k) ≃ₗ[k] (UpperIndex d → k) :=
  { upperCoordinates d with
    invFun := ofUpperCoordinates d
    left_inv := ofUpperCoordinates_upperCoordinates d
    right_inv := upperCoordinates_ofUpperCoordinates d }
/-- The actual submodule of symmetric matrices, including diagonal entries. -/
def symmetricMatrices (d : ℕ) : Submodule k (Matrix (Fin d) (Fin d) k) :=
  {
    carrier := {M | ∀ i j, M i j=M j i}
    zero_mem' := by simp
    add_mem' := by intro M N hM hN i j; simp only [Matrix.add_apply,hM i j,hN i j]
    smul_mem' := by intro u M hM i j; simp only [Matrix.smul_apply,hM i j]
  }

/-- Mirror upper coefficients across the diagonal to obtain an actual symmetric matrix. -/
noncomputable def symmetricOfUpper (d : ℕ) : (UpperIndex d → k) →ₗ[k] symmetricMatrices (k:=k) d :=
  {
    toFun a := ⟨fun i j => if h : i ≤ j then a ⟨(i,j),h⟩ else a ⟨(j,i),le_of_not_ge h⟩, by
      intro i j
      dsimp only
      split_ifs with h1 h2 h2
      · have h : i=j := le_antisymm h1 h2
        subst j
        rfl
      · rfl
      · rfl
      · omega⟩
    map_add' a b := by
      apply Subtype.ext
      ext i j
      simp only [Submodule.coe_add,Matrix.add_apply,Pi.add_apply]
      split_ifs <;> rfl
    map_smul' u a := by
      apply Subtype.ext
      ext i j
      simp only [Submodule.coe_smul,Matrix.smul_apply,Pi.smul_apply,RingHom.id_apply]
      split_ifs <;> rfl
  }

/-- Read the actual upper entries of a symmetric matrix. -/
noncomputable def symmetricUpper (d : ℕ) : symmetricMatrices (k:=k) d →ₗ[k] (UpperIndex d → k) :=
  {
    toFun M p := M.val p.val.1 p.val.2
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }

/-- Mirroring and reading the upper entries are inverse operations. -/
theorem symmetricUpper_ofUpper (d : ℕ) (a : UpperIndex d → k) :
    symmetricUpper d (symmetricOfUpper d a)=a := by
  funext p
  change (if h : p.val.1 ≤ p.val.2 then a ⟨(p.val.1,p.val.2),h⟩
    else a ⟨(p.val.2,p.val.1),le_of_not_ge h⟩)=a p
  rw [dite_eq_left p.property]
  congr 1

/-- Reading and mirroring reconstruct the original symmetric matrix. -/
theorem symmetricOfUpper_upper (d : ℕ) (M : symmetricMatrices (k:=k) d) :
    symmetricOfUpper d (symmetricUpper d M)=M := by
  apply Subtype.ext
  ext i j
  simp only [symmetricOfUpper,symmetricUpper,LinearMap.coe_mk,AddHom.coe_mk]
  split_ifs
  · rfl
  · exact M.property j i

/-- Symmetric matrices have the same full upper-coordinate space in every characteristic. -/
noncomputable def symmetricUpperEquiv (d : ℕ) :
    symmetricMatrices (k:=k) d ≃ₗ[k] (UpperIndex d → k) :=
  { symmetricUpper d with
    invFun := symmetricOfUpper d
    left_inv := symmetricOfUpper_upper d
    right_inv := symmetricUpper_ofUpper d }

/-- The once-per-upper-entry pairing of actual quadratic forms and symmetric matrices. -/
noncomputable def matrixPairing (d : ℕ) (Q : QuadraticForm k (Fin d → k))
    (M : symmetricMatrices (k:=k) d) : k :=
  ∑ p : UpperIndex d, upperCoordinates d Q p * symmetricUpper d M p

/-- Testing the pairing against a single mirrored upper entry reads the corresponding coefficient. -/
theorem matrixPairing_single_right (d : ℕ) (Q : QuadraticForm k (Fin d → k)) (p : UpperIndex d) :
    matrixPairing d Q (symmetricOfUpper d (Pi.single p 1))=upperCoordinates d Q p := by
  simp [matrixPairing,symmetricUpper_ofUpper,Pi.single_apply]

/-- Testing against a single quadratic monomial reads the corresponding actual matrix entry. -/
theorem matrixPairing_single_left (d : ℕ) (M : symmetricMatrices (k:=k) d) (p : UpperIndex d) :
    matrixPairing d (ofUpperCoordinates d (Pi.single p 1)) M=symmetricUpper d M p := by
  simp [matrixPairing,upperCoordinates_ofUpperCoordinates,Pi.single_apply]

/-- The actual pairing detects every quadratic form, including characteristic-two squares. -/
theorem matrixPairing_left_nondegenerate (d : ℕ) (Q : QuadraticForm k (Fin d → k)) :
    (∀ M : symmetricMatrices (k:=k) d, matrixPairing d Q M=0) ↔ Q=0 := by
  constructor
  · intro h
    apply upperCoordinates_injective d
    funext p
    simpa only [matrixPairing_single_right,map_zero,Pi.zero_apply] using
      h (symmetricOfUpper d (Pi.single p 1))
  · rintro rfl
    simp [matrixPairing]

/-- The actual pairing detects every symmetric matrix, including its diagonal in characteristic two. -/
theorem matrixPairing_right_nondegenerate (d : ℕ) (M : symmetricMatrices (k:=k) d) :
    (∀ Q : QuadraticForm k (Fin d → k), matrixPairing d Q M=0) ↔ M=0 := by
  constructor
  · intro h
    apply (symmetricUpperEquiv d).injective
    change symmetricUpper d M = symmetricUpper d 0
    funext p
    simpa only [matrixPairing_single_left,map_zero,Pi.zero_apply] using
      h (ofUpperCoordinates d (Pi.single p 1))
  · rintro rfl
    simp [matrixPairing]
/-- The concrete perfect pairing is linear separately in the form and the symmetric matrix. -/
noncomputable def matrixPairingLinear (d : ℕ) :
    QuadraticForm k (Fin d → k) →ₗ[k] symmetricMatrices (k:=k) d →ₗ[k] k :=
  LinearMap.mk₂ k (matrixPairing d)
    (by intro Q R M; simp [matrixPairing,add_mul,Finset.sum_add_distrib])
    (by intro u Q M; simp [matrixPairing,smul_eq_mul,mul_assoc,Finset.mul_sum])
    (by intro Q M N; simp [matrixPairing,mul_add,Finset.sum_add_distrib])
    (by intro u Q M; simp [matrixPairing,smul_eq_mul,mul_left_comm,Finset.mul_sum])
/-- The concrete symmetric rank-one matrix of a coordinate vector. -/
def rankOneMatrix (d : ℕ) (x : Fin d → k) : symmetricMatrices (k:=k) d :=
  ⟨fun i j => x i*x j, fun i j => mul_comm _ _⟩

/-- Pairing with the actual rank-one matrix evaluates the quadratic form. -/
theorem matrixPairing_rankOne (d : ℕ) (Q : QuadraticForm k (Fin d → k)) (x : Fin d → k) :
    matrixPairing d Q (rankOneMatrix d x)=Q x := by
  have h := congrArg (fun R : QuadraticForm k (Fin d → k) => R x)
    (ofUpperCoordinates_upperCoordinates d Q)
  simpa only [ofUpperCoordinates_apply,matrixPairing,symmetricUpper,rankOneMatrix,
    LinearMap.coe_mk,AddHom.coe_mk] using h
end BinaryFieldCounterexamples.QuadraticCoordinates
