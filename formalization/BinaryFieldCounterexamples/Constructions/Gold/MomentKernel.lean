/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.MatrixRank
public import Mathlib.Data.Fintype.Prod
/-!
# The concrete moment kernel and its dimension

These bounds concern the actual prescribed-domain tensor moments and polar map.
They do not assume the still-unproved number of minimum-rank tensors.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open scoped BigOperators
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- Each literal Gold moment is binary-linear in the tensor coordinates. -/
noncomputable def goldMomentLinearMap (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (r : ℕ) :
    (TensorIndex d → ZMod 2) →ₗ[ZMod 2] B :=
  { toFun := fun A => goldMoment D v A r
    map_add' := by
      intro A C
      simp only [goldMoment, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c A
      rcases binary_eq_zero_or_one c with rfl | rfl <;> simp [goldMoment] }

/-- The actual first `t-1` moment equations, with no abstract constraints. -/
noncomputable def goldMomentConstraints (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) :
    (TensorIndex d → ZMod 2) →ₗ[ZMod 2] (Fin (t-1) → B) :=
  LinearMap.pi (fun r : Fin (t-1) => goldMomentLinearMap D v (r.val+1))

/-- The concrete binary linear code cut out by the Gold moment equations. -/
noncomputable def goldMomentKernel (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) :
    Submodule (ZMod 2) (TensorIndex d → ZMod 2) :=
  LinearMap.ker (goldMomentConstraints D v t)

theorem mem_goldMomentKernel (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t : ℕ) (A : TensorIndex d → ZMod 2) :
    A ∈ goldMomentKernel D v t ↔ ∀ r : ℕ, 1≤r → r<t → goldMoment D v A r=0 := by
  constructor
  · intro h r hr hrt
    have hi : r-1<t-1 := by omega
    have he := congrFun h ⟨r-1,hi⟩
    change goldMoment D v A (r-1+1)=0 at he
    simpa only [Nat.sub_add_cancel hr] using he
  · intro h
    apply funext
    intro r
    change goldMoment D v A (r.val+1)=0
    exact h _ (by omega) (by have := r.isLt; omega)

theorem card_tensorIndex (d : ℕ) : Fintype.card (TensorIndex d)=d.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin d))

/-- Rank-nullity bounds the codimension by the actual number of field-valued
moment equations. No rank-distribution assertion is assumed. -/
theorem goldMomentKernel_finrank_lower_bound (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t m : ℕ) (hB : Fintype.card B=2^m) :
    d.choose 2-m*(t-1) ≤ Module.finrank (ZMod 2) (goldMomentKernel D v t) := by
  have hdim : Module.finrank (ZMod 2) B=m := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := B)
    simp only [Nat.card_eq_fintype_card, ZMod.card, hB] at he
    apply Nat.le_antisymm
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he.ge
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he.le
  have hcod : Module.finrank (ZMod 2) (Fin (t-1) → B)=m*(t-1) := by
    rw [Module.finrank_pi_fintype]
    simp [hdim,Nat.mul_comm]
  have hrange := Submodule.finrank_le (LinearMap.range (goldMomentConstraints D v t))
  rw [hcod] at hrange
  have he := (goldMomentConstraints D v t).finrank_range_add_finrank_ker
  rw [Module.finrank_pi,card_tensorIndex] at he
  change _ ≤ Module.finrank (ZMod 2) (LinearMap.ker (goldMomentConstraints D v t))
  omega

/-- The moment code therefore contains at least the stated binary power. -/
theorem goldMomentKernel_card_lower_bound (D : AddSubgroup B) {d : ℕ}
    (v : Fin d → parameterDomain D) (t m : ℕ) (hB : Fintype.card B=2^m) :
    2^(d.choose 2-m*(t-1)) ≤ Nat.card (goldMomentKernel D v t) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp only [Nat.card_eq_fintype_card,ZMod.card]
  exact Nat.pow_le_pow_right (by decide) (goldMomentKernel_finrank_lower_bound D v t m hB)
end BinaryFieldCounterexamples.Gold
