/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
/-!
# Actual hyperbolic splitting in every characteristic

A singular vector outside the polar kernel has an isotropic partner after
scaling and a quadratic correction. The explicit orthogonal projection gives
a linear splitting and an actual quadratic isometry to the complement plus
the standard hyperbolic plane. No inversion of two or equality between the
quadratic radical and the polar kernel is used.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
open Module
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The polar form is symmetric in every characteristic. -/
theorem polar_symm (Q : QuadraticForm k V) (x y : V) : Q.polarBilin x y=Q.polarBilin y x := by
  exact QuadraticMap.polar_comm Q x y

/-- A singular vector has zero polar self-pairing in every characteristic. -/
theorem polar_self_of_singular (Q : QuadraticForm k V) (x : V) (hx : Q x=0) :
    Q.polarBilin x x=0 := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,hx,smul_zero]

/-- A singular vector outside the polar kernel extends to an actual hyperbolic pair. -/
theorem exists_hyperbolic_partner (Q : QuadraticForm k V) (x : V) (hx : Q x=0)
    (hxp : x ∉ Q.polarBilin.ker) : ∃ y : V, Q y=0 ∧ Q.polarBilin x y=1 := by
  obtain ⟨z,hz⟩ : ∃ z, Q.polarBilin x z≠0 := by
    by_contra h
    apply hxp
    ext z
    simpa using not_exists.mp h z
  let z' := (Q.polarBilin x z)⁻¹ • z
  have hxz : Q.polarBilin x z'=1 := by
    change Q.polarBilin x ((Q.polarBilin x z)⁻¹ • z)=1
    rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hz]
  have hzx : Q.polarBilin z' x=1 := (polar_symm Q _ _).trans hxz
  refine ⟨z'-(Q z') • x,?_,?_⟩
  · have hcorr : Q ((Q z') • x)=0 := by rw [Q.map_smul,hx,smul_zero]
    rw [sub_eq_add_neg,QuadraticMap.map_add Q,Q.map_neg,hcorr,add_zero]
    change Q z'+Q.polarBilin z' (-((Q z') • x))=0
    rw [(Q.polarBilin z').map_neg,(Q.polarBilin z').map_smul,hzx]
    simp
  · simp only [map_sub,map_smul,polar_self_of_singular Q x hx,hxz,smul_zero,sub_zero]

/-- The concrete orthogonal complement of the selected hyperbolic vectors. -/
def hyperbolicComplement (Q : QuadraticForm k V) (x y : V) : Submodule k V :=
  (Q.polarBilin x).ker ⊓ (Q.polarBilin y).ker

/-- Subtract the actual hyperbolic coordinates to project onto their orthogonal complement. -/
def hyperbolicProjection (Q : QuadraticForm k V) (x y : V) : V →ₗ[k] V :=
  LinearMap.id-(Q.polarBilin y).smulRight x-(Q.polarBilin x).smulRight y

/-- The explicit projection lands in the actual orthogonal complement. -/
theorem hyperbolicProjection_mem (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) (z : V) :
    hyperbolicProjection Q x y z ∈ hyperbolicComplement Q x y := by
  have hyx := (polar_symm Q y x).trans hxy
  constructor
  · change Q.polarBilin x (z-(Q.polarBilin y z) • x-(Q.polarBilin x z) • y)=0
    simp only [map_sub,map_smul,polar_self_of_singular Q x hx,hxy,
      smul_eq_mul,mul_zero,mul_one,sub_zero,sub_self]
  · change Q.polarBilin y (z-(Q.polarBilin y z) • x-(Q.polarBilin x z) • y)=0
    simp only [map_sub,map_smul,polar_self_of_singular Q y hy,hyx,
      smul_eq_mul,mul_zero,mul_one,sub_self]

/-- The actual linear splitting with inverse h+a x+b y. -/
noncomputable def hyperbolicSplitEquiv (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    V ≃ₗ[k] hyperbolicComplement Q x y × (k × k) := by
  let p := (hyperbolicProjection Q x y).codRestrict _ (hyperbolicProjection_mem Q x y hx hy hxy)
  let f := p.prod ((Q.polarBilin y).prod (Q.polarBilin x))
  refine { f with
    invFun := fun w => (w.1 : V)+w.2.1 • x+w.2.2 • y
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    change (z-(Q.polarBilin y z) • x-(Q.polarBilin x z) • y)+
      (Q.polarBilin y z) • x+(Q.polarBilin x z) • y=z
    abel
  · intro w
    have hxw : Q.polarBilin x (w.1 : V)=0 := w.1.property.1
    have hyw : Q.polarBilin y (w.1 : V)=0 := w.1.property.2
    have hyx := (polar_symm Q y x).trans hxy
    have hxx := polar_self_of_singular Q x hx
    have hyy := polar_self_of_singular Q y hy
    apply Prod.ext
    · apply Subtype.ext
      change hyperbolicProjection Q x y ((w.1 : V)+w.2.1 • x+w.2.2 • y)=(w.1 : V)
      simp only [hyperbolicProjection,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.smulRight_apply,
        map_add,map_smul,hxw,hyw,hxx,hyy,hxy,hyx]
      abel_nf
      simp
    · apply Prod.ext
      · change Q.polarBilin y ((w.1 : V)+w.2.1 • x+w.2.2 • y)=w.2.1
        simp only [map_add,map_smul,hyw,hyx,hyy,smul_eq_mul,mul_zero,mul_one,add_zero,zero_add]
      · change Q.polarBilin x ((w.1 : V)+w.2.1 • x+w.2.2 • y)=w.2.2
        simp only [map_add,map_smul,hxw,hxy,hxx,smul_eq_mul,mul_zero,mul_one,add_zero,zero_add]

/-- The quadratic form splits literally as the complement form plus a hyperbolic product. -/
theorem quadratic_hyperbolic_decomposition (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1)
    (w : hyperbolicComplement Q x y) (a b : k) :
    Q ((w : V)+a • x+b • y)=Q (w : V)+a*b := by
  have hwx : Q.polarBilin (w : V) x=0 := (polar_symm Q _ _).trans w.property.1
  have hwy : Q.polarBilin (w : V) y=0 := (polar_symm Q _ _).trans w.property.2
  simp only [QuadraticMap.map_add Q,← QuadraticMap.polarBilin_apply_apply,
    Q.map_smul,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,hx,hy,hwx,hwy,hxy,
    zero_add,add_zero,smul_eq_mul,mul_zero,mul_one]
  ring

/-- The standard hyperbolic plane over an arbitrary field. -/
def hyperbolicPlane : QuadraticForm k (k × k) :=
  QuadraticMap.linMulLin (LinearMap.fst k k k) (LinearMap.snd k k k)

/-- The constructed splitting is an actual isometry, without an invertibility-of-two hypothesis. -/
noncomputable def hyperbolicSplitIsometry (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Q.IsometryEquiv ((Q.comp (hyperbolicComplement Q x y).subtype).prod (hyperbolicPlane (k:=k))) :=
  { toLinearEquiv := hyperbolicSplitEquiv Q x y hx hy hxy
    map_app' := by
      intro z
      let e := hyperbolicSplitEquiv Q x y hx hy hxy
      have h := quadratic_hyperbolic_decomposition Q x y hx hy hxy (e z).1 (e z).2.1 (e z).2.2
      change Q (e.symm (e z))=Q ((e z).1 : V)+(e z).2.1*(e z).2.2 at h
      rw [e.symm_apply_apply] at h
      exact h.symm }

/-- Splitting the hyperbolic plane removes exactly two dimensions. -/
theorem hyperbolicComplement_finrank [FiniteDimensional k V] (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Module.finrank k V = Module.finrank k (hyperbolicComplement Q x y)+2 := by
  have h := (hyperbolicSplitEquiv Q x y hx hy hxy).finrank_eq
  simpa [Module.finrank_prod] using h
end BinaryFieldCounterexamples.QuadraticGeometry
