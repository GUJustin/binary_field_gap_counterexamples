/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
public import BinaryFieldCounterexamples.Constructions.DenseAllRates.ScalarZeroCount
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePopulation
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceTranslation
/-!
# Uniform affine restrictions of actual trace-polynomial zero sets

The actual polar rank of each nonzero trace parameter, binary restriction rank
loss, and scalar character orthogonality give a lower zero count on every
prescribed affine binary subspace. Translation and the literal polynomial
representation are kept throughout. No averaging over domains is used.
-/
@[expose] public section
set_option linter.unusedSectionVars false
namespace BinaryFieldCounterexamples.DenseConstruction
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [CharP k 2]
  [Field B] [Fintype B] [CharP B 2] [Algebra k B]
  [Algebra (ZMod 2) k] [Module (ZMod 2) B] [IsScalarTower (ZMod 2) k B]
/-- Every actual scalar quadratic form obeys a uniform affine binary restriction
bound expressed by its actual polar rank. -/
theorem quadratic_affine_zero_lower (Q : QuadraticForm k B)
    (W : Submodule (ZMod 2) B) (v : B) (c d u : ℕ)
    (hcodim : Module.finrank (ZMod 2) B≤Module.finrank (ZMod 2) W+c)
    (hdim : Module.finrank (ZMod 2) W=d)
    (hrank : 2*u+2*c≤Module.finrank (ZMod 2) k*Module.finrank k Q.polarBilin.range) :
    (Nat.card W:ℝ)/(Fintype.card k:ℝ)-
      ((Fintype.card k-1:ℕ):ℝ)*(2^(d-u):ℕ)/(Fintype.card k:ℝ)≤
      (Nat.card {x:W // Q ((x:B)+v)=0}:ℝ) := by
  apply Gold.scalarZeroCount_affine_quadratic_real_lower Q Q.polarBilin Q.map_zero
    _ W v c d u hcodim hdim hrank
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,add_comm y x]
  ring
/-- Nonzero actual trace parameters provide the rank needed for every affine
binary restriction, uniformly over the domain and translation. -/
theorem trace_polynomial_affine_zero_lower
    (ell n t : ℕ) (hq : Fintype.card k=2^ell)
    (ht : 1≤t) (htn : t≤n) (a : QuadraticFormTrace.TraceFamilyIndex n t→B)
    (b z v : B) (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hb : b^((Fintype.card k)^n)=b) (hne : a≠0∨b≠0)
    (W : Submodule (ZMod 2) B) (c d u : ℕ)
    (hcodim : Module.finrank (ZMod 2) B≤Module.finrank (ZMod 2) W+c)
    (hdim : Module.finrank (ZMod 2) W=d) (hrank : 2*u+2*c≤ell*(2*t)) :
    (Nat.card W:ℝ)/(Fintype.card k:ℝ)-
      ((Fintype.card k-1:ℕ):ℝ)*(2^(d-u):ℕ)/(Fintype.card k:ℝ)≤
      (Nat.card {x:W // (QuadraticFormTrace.translatedTracePolynomial (k:=k) n t a b z).eval ((x:B)+v)=0}:ℝ) := by
  let Q:=QuadraticFormTrace.traceFamilyQuadraticForm n t ht htn a b hcard hb
  have hk : Module.finrank (ZMod 2) k=ell := by
    apply Nat.pow_right_injective (by decide : 1<2)
    change 2^Module.finrank (ZMod 2) k=2^ell
    have hh := Module.card_eq_pow_finrank (K:=ZMod 2) (V:=k)
    simpa only [ZMod.card,hq] using hh.symm
  have hQrank := QuadraticFormTrace.traceFamilyQuadraticForm_polar_rank_ge 2 ell hq n t ht htn a b hcard hb hne
  have hcount := quadratic_affine_zero_lower Q W (v-z) c d u hcodim hdim
    (by dsimp only [Q]; rw [hk]; exact le_trans hrank (Nat.mul_le_mul_left ell hQrank))
  have he (x:W) : (QuadraticFormTrace.translatedTracePolynomial (k:=k) n t a b z).eval ((x:B)+v)=0 ↔ Q ((x:B)+(v-z))=0 := by
    rw [QuadraticFormTrace.translatedTracePolynomial_eval,
      ←QuadraticFormTrace.algebraMap_traceFamilyQuadraticForm n t ht htn a b hcard hb]
    rw [map_eq_zero_iff _ (algebraMap k B).injective]
    simp only [Q,add_sub_assoc]
  have hc := Nat.card_congr (Equiv.subtypeEquivRight he)
  rw [hc]
  exact hcount
/-- Counting a predicate on the literal affine domain is exactly counting it
on the binary submodule under translation. -/
theorem affineSubmodule_filter_card (W : Submodule (ZMod 2) B) (v : B) (P : B→Prop) :
    ((affineDomain (additiveDomain W.toAddSubgroup) v).filter P).card=
      Nat.card {x:W // P ((x:B)+v)} := by
  have he : (affineDomain (additiveDomain W.toAddSubgroup) v).filter P=
      (Finset.univ.filter (fun x:W => P ((x:B)+v))).image (fun x:W => (x:B)+v) := by
    ext y
    simp only [affineDomain,additiveDomain,Finset.mem_filter,Finset.mem_image,
      Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hp⟩
      exact ⟨⟨x,hx⟩,hp,rfl⟩
    · rintro ⟨x,hp,rfl⟩
      exact ⟨⟨x.val,x.property,rfl⟩,hp⟩
  rw [he,Finset.card_image_iff.mpr (by
    intro x hx y hy hxy
    exact Subtype.ext (add_right_cancel hxy))]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
end BinaryFieldCounterexamples.DenseConstruction
