/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.QuadraticCharacters
public import BinaryFieldCounterexamples.Constructions.Gold.MatrixRank
public import BinaryFieldCounterexamples.Constructions.Gold.Repairs
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Parity of binary quadratic polar ranks
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

/-- If an integer square is a power of two, its exponent is even. -/
theorem even_exponent_of_int_sq_eq_two_pow (z : ℤ) (n : ℕ)
    (h : z ^ 2 = (2 : ℤ) ^ n) : Even n := by
  have hn : z.natAbs ^ 2 = 2 ^ n := by
    simpa [Int.natAbs_pow] using congrArg Int.natAbs h
  have hf := congrArg (fun m : ℕ ↦ m.factorization 2) hn
  rw [Nat.factorization_pow, Nat.Prime.factorization_pow (by decide : Nat.Prime 2)] at hf
  simp only [Pi.smul_apply, smul_eq_mul, Finsupp.single_eq_same] at hf
  exact ⟨z.natAbs.factorization 2, by simpa [two_mul] using hf.symm⟩

namespace BinaryQuadraticData

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The polar rank of every finite binary quadratic function is even. -/
theorem polar_rank_even (Q : BinaryQuadraticData V) :
    Even (Module.finrank (ZMod 2) (LinearMap.range Q.polarMap)) := by
  let r := Module.finrank (ZMod 2) (LinearMap.range Q.polarMap)
  let d := Module.finrank (ZMod 2) V
  let l : Module.Dual (ZMod 2) V := Subspace.dualLift Q.radical Q.radicalValue
  have hl : l ∈ Q.repairs := by
    apply (mem_repairs_iff Q l).mpr
    intro x
    have hm := LinearMap.congr_fun (Subspace.dualRestrict_comp_dualLift Q.radical)
      Q.radicalValue
    have hx := LinearMap.congr_fun hm x
    change Q.toFun (x : V) + l x = 0
    have hlx : l x = Q.radicalValue x := by
      simpa [l, Submodule.dualRestrict_apply] using hx
    rw [hlx]
    change Q.toFun (x : V) + Q.toFun (x : V) = 0
    exact CharTwo.add_self_eq_zero _
  have hs := walshSum_sq_of_mem_repairs Q l hl
  have hrle : r ≤ d := by
    have hr := Q.polarMap.finrank_range_add_finrank_ker
    omega
  have hV : Nat.card V = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
  have hrad : Nat.card Q.radical = 2 ^ (d - r) := by
    rw [card_radical_of_polarRank Q r rfl, hV,
      Nat.pow_div hrle (by decide : 0 < 2)]
  rw [hV, hrad] at hs
  norm_num at hs
  rw [← pow_add] at hs
  have heven := even_exponent_of_int_sq_eq_two_pow
    (walshSum fun x ↦ Q.toFun x + l x) (d + (d - r)) hs
  rcases heven with ⟨s, hs⟩
  refine ⟨d - s, ?_⟩
  omega

end BinaryQuadraticData

/-- The intrinsic polar rank of every concrete Gold tensor is even. -/
theorem tensorPolarRank_even
    {B : Type*} [Field B] [Fintype B] [CharP B 2] [Algebra (ZMod 2) B]
    (D : AddSubgroup B) [Fintype D] {d : ℕ}
    (v : Fin d → parameterDomain D) (A : TensorCoordinates d) :
    Even (tensorPolarRank D v A) := by
  let Q : BinaryQuadraticData D := BinaryQuadraticData.mk
    (tensorQuadraticFunction D v A) (tensorPolarLinearMap D v A)
    (tensorQuadraticFunction_zero D v A) (tensorQuadraticFunction_add D v A)
  have h := BinaryQuadraticData.polar_rank_even Q
  change Even (Module.finrank (ZMod 2)
    (LinearMap.range (tensorPolarLinearMap D v A))) at h
  rwa [tensorPolarLinearMap_finrank_range] at h

end BinaryFieldCounterexamples.Gold
