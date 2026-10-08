/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.ZeroClassification
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.RadicalQuotient
/-!
# Reduction along an actual nonradical singular line

Inside the singular vector's perpendicular hyperplane, projection along the
selected hyperbolic partner has kernel exactly the singular line. The induced
quotient isometry identifies its dimension, quadratic radical, rank, and zero
count with the actual hyperbolic complement, in every characteristic.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticGeometry
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
/-- The singular line inside the actual perpendicular hyperplane. -/
def singularPerpLine (Q : QuadraticForm k V) (x : V) (hx : Q x=0) :
    Submodule k (Q.polarBilin x).ker :=
  k ∙ (⟨x,polar_self_of_singular Q x hx⟩ : (Q.polarBilin x).ker)
/-- The line lies in the quadratic radical of the restricted form. -/
theorem singularPerpLine_le_radical (Q : QuadraticForm k V) (x : V) (hx : Q x=0) :
    singularPerpLine Q x hx ≤ (Q.comp (Q.polarBilin x).ker.subtype).radical := by
  rw [singularPerpLine,Submodule.span_singleton_le_iff_mem]
  refine ⟨hx,?_⟩
  ext z
  exact z.property
/-- Projection of the perpendicular hyperplane onto the actual hyperbolic complement. -/
noncomputable def singularPerpProjection (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    (Q.polarBilin x).ker →ₗ[k] hyperbolicComplement Q x y :=
  ((hyperbolicProjection Q x y).codRestrict _ (hyperbolicProjection_mem Q x y hx hy hxy)).comp
    (Q.polarBilin x).ker.subtype
/-- The projection kernel is literally the singular line. -/
theorem singularPerpProjection_ker (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    (singularPerpProjection Q x y hx hy hxy).ker=singularPerpLine Q x hx := by
  ext z
  rw [LinearMap.mem_ker, singularPerpLine,Submodule.mem_span_singleton]
  have hz : Q.polarBilin x (z : V)=0 := z.property
  have hval : ((singularPerpProjection Q x y hx hy hxy z) : V)=
      (z : V)-(Q.polarBilin y (z : V)) • x := by
    change (z.val-Q.polarBilin y z.val • x-Q.polarBilin x z.val • y)=_
    rw [hz,zero_smul,sub_zero]
  constructor
  · intro h
    refine ⟨Q.polarBilin y z.val,?_⟩
    apply Subtype.ext
    have h0 := congrArg Subtype.val h
    rw [hval] at h0
    exact (sub_eq_zero.mp h0).symm
  · rintro ⟨a,ha⟩
    apply Subtype.ext
    rw [hval]
    have hav := congrArg Subtype.val ha
    change a • x=z.val at hav
    rw [←hav,map_smul,(polar_symm Q y x).trans hxy]
    simp
/-- Projection is surjective, as each vector in the complement is already fixed. -/
theorem singularPerpProjection_surjective (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Function.Surjective (singularPerpProjection Q x y hx hy hxy) := by
  intro z
  refine ⟨⟨z.val,z.property.1⟩,?_⟩
  apply Subtype.ext
  change (z.val-Q.polarBilin y z.val • x-Q.polarBilin x z.val • y)=z.val
  rw [z.property.1,z.property.2]
  simp
/-- The actual singular-line quotient is linearly equivalent to the hyperbolic complement. -/
noncomputable def singularLineQuotientEquiv (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    ((Q.polarBilin x).ker ⧸ singularPerpLine Q x hx) ≃ₗ[k] hyperbolicComplement Q x y := by
  let f := singularPerpProjection Q x y hx hy hxy
  have he : singularPerpLine Q x hx=f.ker := (singularPerpProjection_ker Q x y hx hy hxy).symm
  exact (Submodule.quotEquivOfEq _ _ he).trans
    (f.quotKerEquivOfSurjective (singularPerpProjection_surjective Q x y hx hy hxy))
/-- On representatives the quotient equivalence is the literal orthogonal projection. -/
theorem singularLineQuotientEquiv_mk (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) (z : (Q.polarBilin x).ker) :
    singularLineQuotientEquiv Q x y hx hy hxy (Submodule.Quotient.mk z)=
      singularPerpProjection Q x y hx hy hxy z := by
  rfl
/-- Projection preserves the restricted quadratic value. -/
theorem singularPerpProjection_quadratic (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) (z : (Q.polarBilin x).ker) :
    Q (singularPerpProjection Q x y hx hy hxy z : V)=Q (z : V) := by
  have hz : Q.polarBilin x z.val=0 := z.property
  have hzx : Q.polarBilin z.val x=0 := (polar_symm Q _ _).trans hz
  change Q (z.val-Q.polarBilin y z.val • x-Q.polarBilin x z.val • y)=Q z.val
  rw [hz,zero_smul,sub_zero,sub_eq_add_neg]
  simp only [QuadraticMap.map_add Q,←QuadraticMap.polarBilin_apply_apply,
    map_neg,Q.map_neg,Q.map_smul,map_smul,hx,hzx,smul_zero,neg_zero,add_zero]
/-- Quotienting a singular perpendicular hyperplane by its singular line removes exactly a hyperbolic plane. -/
noncomputable def singularLineQuotientIsometry (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    ((Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
      (singularPerpLine_le_radical Q x hx)).IsometryEquiv
        (Q.comp (hyperbolicComplement Q x y).subtype) :=
  { toLinearEquiv := singularLineQuotientEquiv Q x y hx hy hxy
    map_app' := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        exact singularPerpProjection_quadratic Q x y hx hy hxy z }
/-- The singular-line quotient has precisely two fewer dimensions. -/
theorem singularLineQuotient_finrank [FiniteDimensional k V] (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Module.finrank k ((Q.polarBilin x).ker ⧸ singularPerpLine Q x hx)=Module.finrank k V-2 := by
  rw [(singularLineQuotientEquiv Q x y hx hy hxy).finrank_eq]
  have h := hyperbolicComplement_finrank Q x y hx hy hxy
  omega
/-- A vector in the complement is radical there exactly when it is radical in the original form. -/
theorem hyperbolicComplement_mem_radical (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1)
    (z : hyperbolicComplement Q x y) :
    z ∈ (Q.comp (hyperbolicComplement Q x y).subtype).radical ↔ z.val ∈ Q.radical := by
  constructor
  · intro hz
    refine ⟨hz.1,?_⟩
    have hzH (w : hyperbolicComplement Q x y) : Q.polarBilin z.val w.val=0 :=
      congrArg (fun L : hyperbolicComplement Q x y →ₗ[k] k => L w) hz.2
    have hzx : Q.polarBilin z.val x=0 := (polar_symm Q _ _).trans z.property.1
    have hzy : Q.polarBilin z.val y=0 := (polar_symm Q _ _).trans z.property.2
    ext v
    let e := hyperbolicSplitEquiv Q x y hx hy hxy
    rw [←e.symm_apply_apply v]
    change Q.polarBilin z.val ((e v).1.val+(e v).2.1 • x+(e v).2.2 • y)=0
    simp only [map_add,map_smul,hzH,hzx,hzy,smul_zero,add_zero]
  · intro hz
    refine ⟨hz.1,?_⟩
    ext w
    exact congrArg (fun L : V →ₗ[k] k => L w.val) hz.2
/-- Removing a hyperbolic plane preserves the actual quadratic radical. -/
noncomputable def hyperbolicComplementRadicalEquiv (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    (Q.comp (hyperbolicComplement Q x y).subtype).radical ≃ₗ[k] Q.radical := by
  refine {
    toFun := fun z => ⟨z.val.val,(hyperbolicComplement_mem_radical Q x y hx hy hxy z.val).mp z.property⟩
    invFun := fun z => ⟨⟨z.val,?_⟩,?_⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_
    map_smul' := ?_ }
  · intro z w; rfl
  · intro a z; rfl
  · constructor
    · exact (polar_symm Q x z.val).trans (congrArg (fun L : V →ₗ[k] k => L x) z.property.2)
    · exact (polar_symm Q y z.val).trans (congrArg (fun L : V →ₗ[k] k => L y) z.property.2)
  · exact (hyperbolicComplement_mem_radical Q x y hx hy hxy _).mpr z.property
  · intro z; rfl
  · intro z; rfl
/-- The singular-line quotient has the same radical dimension as the original form. -/
theorem singularLineQuotient_radical_finrank [FiniteDimensional k V]
    (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Module.finrank k (((Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
      (singularPerpLine_le_radical Q x hx)).radical)=Module.finrank k Q.radical := by
  have h := QuadraticMap.Equivalent.rank_radical_eq
    (Nonempty.intro (singularLineQuotientIsometry Q x y hx hy hxy))
  exact h.trans (hyperbolicComplementRadicalEquiv Q x y hx hy hxy).finrank_eq
/-- The actual quadratic rank drops by exactly two upon singular-line reduction. -/
theorem singularLineQuotient_rank [FiniteDimensional k V] (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Module.finrank k ((Q.polarBilin x).ker ⧸ singularPerpLine Q x hx)-
      Module.finrank k (((Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
        (singularPerpLine_le_radical Q x hx)).radical)=
      (Module.finrank k V-Module.finrank k Q.radical)-2 := by
  rw [singularLineQuotient_finrank Q x y hx hy hxy,
    singularLineQuotient_radical_finrank Q x y hx hy hxy]
  omega
/-- The zero count transforms through the actual singular-line quotient by the hyperbolic recurrence. -/
theorem singularLineQuotient_zero_count [Fintype k] [Fintype V]
    (Q : QuadraticForm k V) (x y : V)
    (hx : Q x=0) (hy : Q y=0) (hxy : Q.polarBilin x y=1) :
    Nat.card {z : V // Q z=0} =
      (Fintype.card k-1)*(Fintype.card k)^(Module.finrank k V-2)+
      Fintype.card k * Nat.card {z : (Q.polarBilin x).ker ⧸ singularPerpLine Q x hx //
        (Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
          (singularPerpLine_le_radical Q x hx) z=0} := by
  classical
  let e := singularLineQuotientIsometry Q x y hx hy hxy
  have hz : Nat.card {z : (Q.polarBilin x).ker ⧸ singularPerpLine Q x hx //
      (Q.comp (Q.polarBilin x).ker.subtype).lift (singularPerpLine Q x hx)
        (singularPerpLine_le_radical Q x hx) z=0} =
      Nat.card {z : hyperbolicComplement Q x y // Q z.val=0} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv e.toEquiv (fun z => by
      change _ ↔ (Q.comp (hyperbolicComplement Q x y).subtype) (e z)=0
      rw [e.map_app])
  rw [hz,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  rw [hyperbolicSplit_zero_count Q x y hx hy hxy]
  have hd := hyperbolicComplement_finrank Q x y hx hy hxy
  have hcard := Module.card_eq_pow_finrank (K:=k) (V:=hyperbolicComplement Q x y)
  rw [hcard]
  congr 3
  omega
end BinaryFieldCounterexamples.QuadraticGeometry
