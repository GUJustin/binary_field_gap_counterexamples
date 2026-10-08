/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.EllipticType
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Affine quadratic level sets and literal translations

The paragraph after Corollary 5.23 distinguishes uniform level sets, obtained
when a linear term is nonzero on a quadratic-radical direction, from translated
quadratic level sets. When the linear term vanishes on the polar kernel, it is
a polar pairing with a vector, and translation by that vector removes it.
All equivalences use the actual points of the paper's level sets.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
attribute [local instance] Classical.propDecidable

variable {k V : Type*} [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]

/-- The paragraph after Corollary 5.23: a linear term vanishing on the polar
kernel is pairing with an actual translation vector. -/
theorem exists_polar_shift_of_vanishes_kernel (Q : QuadraticForm k V) (L : V →ₗ[k] k)
    (hL : ∀ u ∈ Q.polarBilin.ker, L u = 0) :
    ∃ v : V, L = Q.polarBilin v := by
  have hm : L ∈ Q.polarBilin.ker.dualAnnihilator :=
    (Submodule.mem_dualAnnihilator L).mpr hL
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hm
  obtain ⟨v,hv⟩ := hm
  refine ⟨v,?_⟩
  ext x
  have he := congrArg (fun l : V →ₗ[k] k => l x) hv
  simpa only [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm] using he.symm

omit [Fintype k] [Fintype V] in
theorem polar_shift_identity (Q : QuadraticForm k V) (L : V →ₗ[k] k)
    (v : V) (hL : L = Q.polarBilin v) (x : V) :
    Q (x+v) = Q x + L x + Q v := by
  rw [QuadraticMap.map_add Q x v, hL, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_comm Q x v]
  abel

/-- The paragraph after Corollary 5.23: the actual affine-quadratic fiber
is equivalent to the quadratic fiber at `a-c+Q(v)`, by `x↦x+v`. -/
noncomputable def affineQuadraticLevelShiftEquiv (Q : QuadraticForm k V)
    (L : V →ₗ[k] k) (c a : k) (v : V) (hL : L = Q.polarBilin v) :
    {x : V // Q x + L x + c = a} ≃ {y : V // Q y = a-c+Q v} :=
  { toFun := fun x => ⟨x+v, by
      rw [polar_shift_identity Q L v hL]
      linear_combination x.property⟩
    invFun := fun y => ⟨y-v, by
      have h := polar_shift_identity Q L v hL (y-v)
      rw [sub_add_cancel] at h
      linear_combination y.property - h⟩
    left_inv := fun x => Subtype.ext (add_sub_cancel_right (x : V) v)
    right_inv := fun y => Subtype.ext (sub_add_cancel (y : V) v) }

omit [Fintype k] [Fintype V] in
theorem affine_shift_along_radical (Q : QuadraticForm k V)
    (L : V →ₗ[k] k) (c : k) (u : V) (hu : u ∈ Q.radical) (x : V) (t : k) :
    Q (x+t • u)+L (x+t • u)+c = Q x+L x+c+t*L u := by
  have hrad := (QuadraticMap.mem_radical_iff').mp (Q.radical.smul_mem t hu)
  rw [add_comm x (t • u),hrad.2, map_add, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The paragraph after Corollary 5.23: a nonzero linear term on a
quadratic-radical direction makes every level set have exactly `|V|/|k|`
points, expressed without division. -/
theorem affineQuadratic_level_card_of_radical_direction
    (Q : QuadraticForm k V) (L : V →ₗ[k] k) (c a : k) (u : V)
    (hu : u ∈ Q.radical) (hLu : L u ≠ 0) :
    Fintype.card k * Fintype.card {x : V // Q x+L x+c=a} = Fintype.card V := by
  classical
  let f := fun x : V => Q x+L x+c
  have hf (x : V) (t : k) : f (x+t • u) = f x+t*L u :=
    affine_shift_along_radical Q L c u hu x t
  let e : V ≃ k × {x : V // f x=a} :=
    { toFun := fun x => (f x, ⟨x+((a-f x)/L u) • u, by
        rw [hf]
        rw [div_mul_cancel₀ _ hLu]
        ring⟩)
      invFun := fun y => y.2+((y.1-a)/L u) • u
      left_inv := by
        intro x
        change (x+((a-f x)/L u) • u)+((f x-a)/L u) • u=x
        rw [add_assoc, ←add_smul]
        have he : (a-f x)/L u+(f x-a)/L u=0 := by ring
        rw [he,zero_smul,add_zero]
      right_inv := by
        rintro ⟨b,x⟩
        have hfb : f (x+((b-a)/L u) • u)=b := by
          rw [hf,x.property]
          rw [div_mul_cancel₀ _ hLu]
          ring
        apply Prod.ext
        · exact hfb
        · apply Subtype.ext
          change (x+((b-a)/L u) • u)+((a-f (x+((b-a)/L u) • u))/L u) • u=x
          rw [hfb,add_assoc,←add_smul]
          have he : (b-a)/L u+(a-b)/L u=0 := by ring
          rw [he,zero_smul,add_zero] }
  simpa only [Fintype.card_prod] using (Fintype.card_congr e).symm

end BinaryFieldCounterexamples.QuadraticGeometry
