/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rank loss under restriction

Restricting both arguments of a finite-dimensional bilinear form to a
codimension-`c` subspace lowers its rank by at most `2c`.  The proof separates
the losses from restricting the domain and restricting the resulting dual
functional.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold
open LinearMap
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Restrict both arguments of a linearized bilinear form to a subspace. -/
def restrictPolarMap
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (C : V →ₗ[K] Module.Dual K V) :
    W →ₗ[K] Module.Dual K W :=
  W.dualRestrict.comp (C.comp W.subtype)

/-- Restricting the domain loses at most the codimension of the subspace. -/
theorem finrank_range_le_restrictDomain_add_codim
    {K U Y : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup Y] [Module K Y]
    (W : Submodule K U) (f : U →ₗ[K] Y) (c : ℕ)
    (hcodim : Module.finrank K U ≤ Module.finrank K W + c) :
    Module.finrank K (LinearMap.range f) ≤
      Module.finrank K (LinearMap.range (f.comp W.subtype)) + c := by
  let j : LinearMap.ker (f.comp W.subtype) →ₗ[K] LinearMap.ker f :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f ↦ z.1) hxy
  have hker : Module.finrank K (LinearMap.ker (f.comp W.subtype)) ≤
      Module.finrank K (LinearMap.ker f) :=
    LinearMap.finrank_le_finrank_of_injective hj
  have hf := f.finrank_range_add_finrank_ker
  have hfw := (f.comp W.subtype).finrank_range_add_finrank_ker
  have hW : Module.finrank K W ≤ Module.finrank K U := W.finrank_le
  omega

/-- Postcomposition loses at most the dimension of the postcomposed map's
kernel. -/
theorem finrank_range_le_comp_add_ker
    {K U V Y : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Y] [Module K Y]
    (f : U →ₗ[K] V) (g : V →ₗ[K] Y) :
    Module.finrank K (LinearMap.range f) ≤
      Module.finrank K (LinearMap.range (g.comp f)) +
        Module.finrank K (LinearMap.ker g) := by
  let q : LinearMap.ker (g.comp f) →ₗ[K] LinearMap.ker g :=
    { toFun := fun x ↦ ⟨f x.1, x.2⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro a x; apply Subtype.ext; simp }
  have hkerq : Module.finrank K (LinearMap.ker q) ≤
      Module.finrank K (LinearMap.ker f) := by
    let j : LinearMap.ker q →ₗ[K] LinearMap.ker f :=
      { toFun := fun x ↦ ⟨x.1.1, by
          have hx := x.2
          change q x.1 = 0 at hx
          exact congrArg Subtype.val hx⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    apply LinearMap.finrank_le_finrank_of_injective (f := j)
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    change (x.1.1 : U) = y.1.1 at hv
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  have hqrange : Module.finrank K (LinearMap.range q) ≤
      Module.finrank K (LinearMap.ker g) := (LinearMap.range q).finrank_le
  have hq := q.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hgf := (g.comp f).finrank_range_add_finrank_ker
  omega

/-- Restricting both arguments of a bilinear form to a codimension-`c`
subspace lowers its rank by at most `2c`. -/
theorem polar_rank_le_restriction_add_two_codim
    {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Submodule K V) (C : V →ₗ[K] Module.Dual K V) (c : ℕ)
    (hcodim : Module.finrank K V ≤ Module.finrank K W + c) :
    Module.finrank K (LinearMap.range C) ≤
      Module.finrank K (LinearMap.range (restrictPolarMap W C)) + 2 * c := by
  let f := C.comp W.subtype
  have hdom := finrank_range_le_restrictDomain_add_codim W C c hcodim
  have hpost := finrank_range_le_comp_add_ker f W.dualRestrict
  have hg := W.dualRestrict.finrank_range_add_finrank_ker
  have hsurj : LinearMap.range W.dualRestrict = ⊤ :=
    LinearMap.range_eq_top.mpr Subspace.dualRestrict_surjective
  have hdualV := Subspace.dual_finrank_eq (K := K) (V := V)
  have hdualW := Subspace.dual_finrank_eq (K := K) (V := W)
  rw [hsurj, finrank_top, hdualW, hdualV] at hg
  dsimp only [f] at hpost
  change Module.finrank K (LinearMap.range C) ≤
    Module.finrank K (LinearMap.range (W.dualRestrict.comp (C.comp W.subtype))) + 2*c
  omega

end BinaryFieldCounterexamples.Gold
