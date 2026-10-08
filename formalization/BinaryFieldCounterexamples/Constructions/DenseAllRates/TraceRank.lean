/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.FieldTheory.Finite.Trace
public import BinaryFieldCounterexamples.Constructions.Gold.RankRestriction

/-!
# Binary ranks of traced bilinear forms

For a finite field of characteristic two, tracing a nonzero scalar multiple of
a field-valued bilinear form to the prime field does not enlarge its radical.
Consequently its binary rank is its original rank times the extension degree.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold
open LinearMap
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def binaryTracePolarMap
    {k V : Type*} [Field k] [Finite k] [CharP k 2]
    [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    (v : k) (C : V →ₗ[k] Module.Dual k V) :
    V →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
  { toFun := fun x ↦ (Algebra.trace (ZMod 2) k).comp
      ((LinearMap.mulLeft (ZMod 2) v).comp ((C x).restrictScalars (ZMod 2)))
    map_add' := by
      intro x y
      ext z
      simp [LinearMap.mulLeft_apply]
    map_smul' := by
      intro a x
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply]
      change Algebra.trace (ZMod 2) k (v * C (a • x) y) =
        a • Algebra.trace (ZMod 2) k (v * C x y)
      rw [C.map_smul_of_tower, LinearMap.smul_apply, mul_smul_comm]
      exact (Algebra.trace (ZMod 2) k).map_smul a (v * C x y) }

theorem ker_binaryTracePolarMap
    {k V : Type*} [Field k] [Finite k] [CharP k 2]
    [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    (v : k) (hv : v ≠ 0) (C : V →ₗ[k] Module.Dual k V) :
    LinearMap.ker (binaryTracePolarMap v C) =
      (LinearMap.ker C).restrictScalars (ZMod 2) := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    by_contra hCx
    have htr := (traceForm_nondegenerate (ZMod 2) k).1 v
    simp_rw [Algebra.traceForm_apply] at htr
    have hex : ∃ b : k, Algebra.trace (ZMod 2) k (v * b) ≠ 0 := by
      by_contra! hall
      exact hv (htr hall)
    obtain ⟨b, hb⟩ := hex
    have hrange := Module.Dual.range_eq_top_of_ne_zero hCx
    have hbmem : b ∈ LinearMap.range (C x) := by rw [hrange]; trivial
    obtain ⟨y, hy⟩ := hbmem
    have hxy := congrArg (fun L : Module.Dual (ZMod 2) V ↦ L y) hx
    change Algebra.trace (ZMod 2) k (v * C x y) = 0 at hxy
    rw [hy] at hxy
    exact hb hxy
  · intro hx
    change C x = 0 at hx
    apply LinearMap.ext
    intro y
    simp [binaryTracePolarMap, hx]

/-- Taking the prime-field trace of a nonzero scalar multiple of a bilinear
form multiplies its rank by the extension degree. -/
theorem binaryTracePolarMap_rank
    {k V : Type*} [Field k] [Finite k] [CharP k 2]
    [Algebra (ZMod 2) k]
    [AddCommGroup V] [Module k V] [Module (ZMod 2) V]
    [IsScalarTower (ZMod 2) k V]
    [FiniteDimensional k V] [FiniteDimensional (ZMod 2) V]
    (v : k) (hv : v ≠ 0) (C : V →ₗ[k] Module.Dual k V) :
    Module.finrank (ZMod 2) k * Module.finrank k (LinearMap.range C) =
      Module.finrank (ZMod 2) (LinearMap.range (binaryTracePolarMap v C)) := by
  have hV := Module.finrank_mul_finrank (ZMod 2) k V
  have hkerK := C.finrank_range_add_finrank_ker
  have hker2 := (binaryTracePolarMap v C).finrank_range_add_finrank_ker
  rw [ker_binaryTracePolarMap v hv C] at hker2
  have hkerMul := Module.finrank_mul_finrank (ZMod 2) k (LinearMap.ker C)
  let e : (LinearMap.ker C).restrictScalars (ZMod 2) ≃ₗ[ZMod 2] LinearMap.ker C :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hrestrict : Module.finrank (ZMod 2)
      ((LinearMap.ker C).restrictScalars (ZMod 2)) =
      Module.finrank (ZMod 2) (LinearMap.ker C) := e.finrank_eq
  rw [hrestrict, ← hkerMul] at hker2
  have hmul : Module.finrank (ZMod 2) k * Module.finrank k (LinearMap.range C) +
      Module.finrank (ZMod 2) k * Module.finrank k (LinearMap.ker C) =
      Module.finrank (ZMod 2) k * Module.finrank k V := by
    rw [← Nat.mul_add, hkerK]
  omega

end BinaryFieldCounterexamples.Gold
