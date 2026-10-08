/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Longfellow.Domain
/-!
# Longfellow's linear bit coordinates and printed power-basis span

These bridges identify the proved literal index domain with the exact
basis-sum and low-coordinate span printed in Section 5.8.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Longfellow
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]

/-- Section 5.8: `inj` on binary digit vectors is an actual binary linear map. -/
noncomputable def bitInjection (b : Module.Basis (Fin 16) (ZMod 2) B) :
    (Fin 16 → ZMod 2) →ₗ[ZMod 2] B := b.equivFun.symm.toLinearMap

/-- Section 5.8: the integer index injection is that linear map applied to its bits. -/
theorem inj_eq_bitInjection (b : Module.Basis (Fin 16) (ZMod 2) B) (j : ℕ) :
    inj b j = bitInjection b (fun i => if j.testBit i then 1 else 0) := by rfl

/-- Section 5.8: in the specification's power basis the injection is exactly
`Σ j_i g^i`, rather than an unspecified binary encoding. -/
theorem inj_eq_power_sum (b : Module.Basis (Fin 16) (ZMod 2) B) (g : B)
    (hg : ∀ i, b i=g^(i : ℕ)) (j : ℕ) :
    inj b j = ∑ i : Fin 16, (if j.testBit i then (1 : ZMod 2) else 0) • g^(i : ℕ) := by
  rw [inj_eq_sum]
  simp_rw [hg]

/-- Section 5.8: the actual low-coordinate map sends the standard binary
basis vector to the corresponding prescribed field basis vector. -/
theorem lowMap_basis (b : Module.Basis (Fin 16) (ZMod 2) B) (i : Fin 11) :
    lowMap b (Pi.basisFun (ZMod 2) (Fin 11) i) = b ⟨i,by omega⟩ := by
  apply b.equivFun.injective
  simp only [lowMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,LinearMap.coe_mk,AddHom.coe_mk]
  funext j
  rw [b.equivFun_self,Pi.basisFun_apply]
  by_cases hj : (j : ℕ)<11
  · simp [hj,Pi.single_apply,Fin.ext_iff,eq_comm]
  · have hne : (i : ℕ) ≠ j := by omega
    simp [hj,Fin.ext_iff,hne]

/-- Section 5.8: the computed eleven-space is precisely the span of the first
eleven basis powers used in the paper's displayed affine-space formula. -/
theorem lowSpace_eq_span (b : Module.Basis (Fin 16) (ZMod 2) B) :
    (lowMap b).range = Submodule.span (ZMod 2)
      (Set.range fun i : Fin 11 => b ⟨i,by omega⟩) := by
  rw [LinearMap.range_eq_map,←(Pi.basisFun (ZMod 2) (Fin 11)).span_eq,
    Submodule.map_span]
  have he : lowMap b '' Set.range (Pi.basisFun (ZMod 2) (Fin 11)) =
      Set.range (fun i : Fin 11 => b ⟨i,by omega⟩) := by
    ext x
    constructor
    · rintro ⟨v,⟨i,rfl⟩,rfl⟩
      exact ⟨i,(lowMap_basis b i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨_,⟨i,rfl⟩,lowMap_basis b i⟩
  rw [he]
end BinaryFieldCounterexamples.Longfellow
