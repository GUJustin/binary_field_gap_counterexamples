/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.MatrixRank
public import BinaryFieldCounterexamples.Constructions.Gold.Distinctness
/-!
# Minimum polar rank from compressed roots

These bounds concern the actual prescribed-domain tensor moments and polar map.
They do not assume the still-unproved number of minimum-rank tensors.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
variable {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
/-- A dual evaluation frame makes every nonzero alternating tensor have a
nonzero additive derivative. -/
theorem tensorLinearPart_ne_zero_of_ne_zero
    (D : AddSubgroup B) {d : ℕ} (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (A : TensorCoordinates d) (hA : A ≠ (fun _ => 0)) : tensorLinearPart D v A ≠ 0 := by
  intro hJ
  apply hA
  apply tensorPolarMap_injective D v x hdual
  ext y z
  have hy : tensorPolarFunctional D v A y = 0 :=
    (tensorPolarFunctional_eq_zero_iff D v A y).mpr (by rw [hJ]; simp)
  change tensorPolarFunctional D v A y z = tensorPolarFunctional D v (fun _ => 0) y z
  rw [hy]
  simp [tensorPolarFunctional]

/-- Moment vanishing forces minimum polar rank on the actual prescribed
domain, by comparing exact radical size with the compressed root bound. -/
theorem tensorPolarRank_lower_bound_of_moments
    (D : AddSubgroup B) [Fintype D] (k : ℕ) (hD : Nat.card D=2^(k+1))
    {d : ℕ} (v : Fin d → parameterDomain D) (x : Fin d → D)
    (hdual : ∀ i j, ((parameterEquiv D).symm (v i)) (x j) = if i=j then 1 else 0)
    (A : TensorCoordinates d) (hA : A ≠ (fun _ => 0)) (t : ℕ) (ht : 2*t≤k+1)
    (hM : ∀ r, 1≤r → r<t → goldMoment D v A r=0) :
    2*t ≤ tensorPolarRank D v A := by
  classical
  let J := tensorLinearPart D v A
  have hne : J≠0 := tensorLinearPart_ne_zero_of_ne_zero D v x hdual A hA
  have hbound : Fintype.card {z : B // J.eval z=0} ≤ 2^(k+1-2*t) := by
    rw [Fintype.card_subtype]
    exact card_tensorLinearPart_roots_le D k hD v A t ht hM hne Finset.univ
  have hdim : Module.finrank (ZMod 2) D=k+1 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D)
    rw [hD] at he
    simp only [Nat.card_eq_fintype_card, ZMod.card] at he
    apply Nat.le_antisymm
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he.ge
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he.le
  have hrle : tensorPolarRank D v A≤k+1 := by
    have h := (tensorPolarMap D v A).finrank_range_add_finrank_ker
    rw [hdim] at h
    change tensorPolarRank D v A+_=_ at h
    omega
  have hsub : Fintype.card {y : D // J.eval (y:B)=0} ≤
      Fintype.card {z : B // J.eval z=0} := by
    apply Fintype.card_le_of_injective (fun y => ⟨(y.val:B),y.property⟩)
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {w : B // J.eval w=0} => z.val) h
  have hexp : 2^(k+1-tensorPolarRank D v A)≤2^(k+1-2*t) := by
    rw [← Nat.card_eq_fintype_card, card_tensorLinearPart_zeros,
      hD, Nat.pow_div hrle (by decide : 0<2)] at hsub
    exact hsub.trans hbound
  have := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hexp
  omega
end BinaryFieldCounterexamples.Gold
