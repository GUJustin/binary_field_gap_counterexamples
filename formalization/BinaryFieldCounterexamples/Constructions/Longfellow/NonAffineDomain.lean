/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Longfellow.Domain
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
/-!
# Longfellow's queried domain is not affine

Section 5.8's actual interval contains the indices 1024, 2048 and 4096.
Their three binary images sum to the image of 7168, outside the interval.
Every binary affine subspace is closed under such triple sums. This proves
non-affineness directly, also after embedding into the challenge field.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow
attribute [local instance] Classical.propDecidable Classical.decEq
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- Section 5.8's four encoded circuit lengths, as used in Table 6. -/
def configuredLengths : Finset ℕ := {4151,4265,4307,4415}

/-- Section 5.8: each configured interval includes the non-affineness witness
and the central affine block, and its `(N,K)` pair is exactly a Table 6 pair. -/
theorem configured_length_bounds (e : ℕ) (he : e ∈ configuredLengths) :
    e < 2^16 ∧ 1≤(e+1)/9 ∧ 2*((e+1)/9)≤e ∧
    2*((e+1)/9)-1≤1024 ∧ 4096<e ∧ e≤7168 ∧
    (e-2*((e+1)/9)+1,(e+1)/9) ∈ parameterPairs := by
  simp only [configuredLengths,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> norm_num [parameterPairs]

/-- Section 5.8: the three explicit inside indices have XOR 7168, hence their
literal binary images have sum `inj(7168)`. -/
theorem inj_nonaffine_witness_sum (b : Module.Basis (Fin 16) (ZMod 2) B) :
    inj b 1024+inj b 2048+inj b 4096=inj b 7168 := by
  apply b.equivFun.injective
  simp only [map_add,inj,LinearEquiv.apply_symm_apply]
  funext i
  fin_cases i <;> decide

/-- Section 5.8: every actual configured queried domain is non-affine, even
when viewed inside the challenge field by its prescribed field embedding. -/
theorem mapped_domain_not_affine
    {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (φ : B →+* F) (b : Module.Basis (Fin 16) (ZMod 2) B)
    (e : ℕ) (he : e ∈ configuredLengths) :
    ¬∃ A : AffineSubspace (ZMod 2) F,
      (A : Set F)=(mappedDomain φ (domain b e ((e+1)/9)) : Set F) := by
  obtain ⟨he16,hK,h2K,hlo,hhi,hupper,hconfig⟩ := configured_length_bounds e he
  have hmem (j : ℕ) (hj : 2*((e+1)/9)-1≤j) (hj' : j<e) :
      φ (inj b j) ∈ mappedDomain φ (domain b e ((e+1)/9)) := by
    apply Finset.mem_image.mpr
    exact ⟨inj b j,Finset.mem_image.mpr ⟨j,Finset.mem_Ico.mpr ⟨hj,hj'⟩,rfl⟩,rfl⟩
  have hnot : φ (inj b 7168) ∉ mappedDomain φ (domain b e ((e+1)/9)) := by
    intro h
    obtain ⟨x,hx,hx'⟩ := Finset.mem_image.mp h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    have heq : j=7168 := inj_injective_below b
      ((Finset.mem_Ico.mp hj).2.trans he16) (by norm_num) (φ.injective hx')
    have hh := (Finset.mem_Ico.mp hj).2
    omega
  rintro ⟨A,hA⟩
  have h1 : φ (inj b 1024) ∈ A := by
    change φ (inj b 1024) ∈ (A : Set F)
    rw [hA]
    exact hmem 1024 hlo (by omega)
  have h2 : φ (inj b 2048) ∈ A := by
    change φ (inj b 2048) ∈ (A : Set F)
    rw [hA]
    exact hmem 2048 (by omega) (by omega)
  have h3 : φ (inj b 4096) ∈ A := by
    change φ (inj b 4096) ∈ (A : Set F)
    rw [hA]
    exact hmem 4096 (by omega) hhi
  have hs := A.smul_vsub_vadd_mem (1 : ZMod 2) h1 h2 h3
  simp only [one_smul,vsub_eq_sub,vadd_eq_add,CharTwo.sub_eq_add,←map_add,
    inj_nonaffine_witness_sum] at hs
  change φ (inj b 7168) ∈ (A : Set F) at hs
  rw [hA] at hs
  exact hnot hs

/-- Section 5.8's rate bound is certified on the actual queried coordinates,
for all four configured circuit lengths. -/
theorem configured_domain_rate_le_seventh (b : Module.Basis (Fin 16) (ZMod 2) B)
    (e : ℕ) (he : e ∈ configuredLengths) :
    (((e+1)/9 : ℕ) : ℚ)/(domain b e ((e+1)/9)).card≤1/7 := by
  obtain ⟨he16,hK,h2K,_⟩ := configured_length_bounds e he
  rw [domain_card b e ((e+1)/9) he16 hK h2K]
  simp only [configuredLengths,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> norm_num

end BinaryFieldCounterexamples.Longfellow
