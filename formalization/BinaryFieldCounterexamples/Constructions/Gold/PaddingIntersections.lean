/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Family
public import Mathlib.GroupTheory.Index
/-!
# Exact intersection and union counts for radical-invariant sets

Uniform fibers of the actual addition homomorphism from `W × H` to the ambient
space show that an `H`-invariant set meets `W` in the exact uniform fraction when
`W + H` is the whole space. Multiplicative cardinal identities avoid division or
rounding and give the exact union gain used by locator padding.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
/-- A surjective homomorphism pulls finite subsets back with exactly uniform fibers. -/
theorem card_preimage_mul_card_of_surjective_addHom
    {U V : Type*} [AddGroup U] [AddGroup V] [Fintype U] [Fintype V]
    (f : U →+ V) (hf : Function.Surjective f) (S : Finset V) :
    (Finset.univ.filter fun x => f x ∈ S).card*Fintype.card V=S.card*Fintype.card U := by
  let c := (Finset.univ.filter fun x : U => f x=0).card
  have hc (T : Finset V) : (Finset.univ.filter fun x => f x ∈ T).card=T.card*c := by
    rw [←Finset.sum_card_fiberwise_eq_card_filter]
    apply Finset.sum_const_nat
    intro y hy
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  have hfull := hc Finset.univ
  simp only [Finset.mem_univ,Finset.filter_true,Finset.card_univ] at hfull
  rw [hc,hfull]
  ring
/-- An invariant set intersects a complementary-sum subspace in the exact uniform fraction. -/
theorem card_intersection_of_radical_invariance
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W H : Submodule (ZMod 2) V) (hWH : W ⊔ H=⊤)
    (S : Finset V) (hS : ∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) :
    (Finset.univ.filter fun w : W => (w:V) ∈ S).card*Fintype.card V=
      S.card*Fintype.card W := by
  let f : W × H →+ V :=
    { toFun := fun z => (z.1:V)+(z.2:V)
      map_zero' := by simp
      map_add' := by intro x y; simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add]; abel }
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ W ⊔ H := by rw [hWH]; trivial
    obtain ⟨w,h,he⟩ := Submodule.mem_sup'.mp hx
    exact ⟨(w,h),he⟩
  have hc := card_preimage_mul_card_of_surjective_addHom f hf S
  have hp : (Finset.univ.filter fun z : W × H => f z ∈ S).card=
      (Finset.univ.filter fun w : W => (w:V) ∈ S).card*Fintype.card H := by
    rw [Finset.card_filter,Fintype.sum_prod_type]
    change (∑ w : W, ∑ h : H, if (w:V)+(h:V) ∈ S then 1 else 0)=_
    simp_rw [hS]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rw [←Finset.mul_sum,←Finset.card_filter,mul_comm]
  rw [hp,Fintype.card_prod] at hc
  apply mul_right_cancel₀ (show Fintype.card H≠0 from (Fintype.card_pos_iff.mpr ⟨0⟩).ne')
  linarith [hc]
/-- The literal subset intersection obeys the exact uniform count. -/
theorem card_finset_intersection_of_radical_invariance
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W H : Submodule (ZMod 2) V) (hWH : W ⊔ H=⊤)
    (S : Finset V) (hS : ∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) :
    ((Finset.univ.filter fun x : V => x ∈ W) ∩ S).card*Fintype.card V=
      S.card*Fintype.card W := by
  have he : (Finset.univ.filter fun w : W => (w:V) ∈ S)=S.subtype (fun x => x ∈ W) := by
    ext w
    simp
  have hi : (Finset.univ.filter fun x : V => x ∈ W) ∩ S=S.filter (fun x => x ∈ W) := by
    ext x
    simp [and_comm]
  rw [hi]
  have hh := card_intersection_of_radical_invariance W H hWH S hS
  rw [he,Finset.card_subtype] at hh
  exact hh
/-- Padding by a complementary-sum subspace gives the exact union-size gain, without rounding. -/
theorem card_union_of_radical_invariance
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W H : Submodule (ZMod 2) V) (hWH : W ⊔ H=⊤)
    (S : Finset V) (hS : ∀ x : V, ∀ h : H, x+(h:V) ∈ S ↔ x ∈ S) :
    ((Finset.univ.filter fun x : V => x ∈ W) ∪ S).card*Fintype.card V=
      Fintype.card W*Fintype.card V+(Fintype.card V-Fintype.card W)*S.card := by
  have hi := card_finset_intersection_of_radical_invariance W H hWH S hS
  have hc := Finset.card_union_add_card_inter (Finset.univ.filter fun x : V => x ∈ W) S
  rw [←Fintype.card_subtype] at hc
  have hw : Fintype.card W≤Fintype.card V := Fintype.card_subtype_le (fun x => x ∈ W)
  have hd : Fintype.card V-Fintype.card W+Fintype.card W=Fintype.card V := Nat.sub_add_cancel hw
  nlinarith [hi,hc]
end BinaryFieldCounterexamples.Gold
