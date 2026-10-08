/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.Polar
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Binary quadratic characters and linear repairs
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold

open scoped BigOperators

/-- A binary quadratic function together with its actual polar linear map. -/
def BinaryQuadraticData (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :=
  {p : (V → ZMod 2) × (V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) //
    p.1 0 = 0 ∧ ∀ x y, p.1 (x + y) = p.1 x + p.1 y + p.2 y x}

namespace BinaryQuadraticData

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Build binary quadratic data from its function, polar map, and laws. -/
def mk (q : V → ZMod 2) (b : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hzero : q 0 = 0) (hadd : ∀ x y, q (x + y) = q x + q y + b y x) :
    BinaryQuadraticData V := ⟨(q, b), hzero, hadd⟩

/-- The quadratic function. -/
def toFun (Q : BinaryQuadraticData V) : V → ZMod 2 := Q.1.1

/-- The linear map representing the polar form. -/
def polarMap (Q : BinaryQuadraticData V) :
    V →ₗ[ZMod 2] Module.Dual (ZMod 2) V := Q.1.2

/-- The quadratic function vanishes at zero. -/
theorem map_zero (Q : BinaryQuadraticData V) : Q.toFun 0 = 0 := by
  exact Q.2.1

/-- The defining polarization identity. -/
theorem map_add_polar (Q : BinaryQuadraticData V) (x y : V) :
    Q.toFun (x + y) = Q.toFun x + Q.toFun y + Q.polarMap y x := by
  exact Q.2.2 x y

/-- The polar radical. -/
def radical (Q : BinaryQuadraticData V) : Submodule (ZMod 2) V :=
  LinearMap.ker Q.polarMap

/-- A quadratic function restricts to a linear functional on its polar radical. -/
def radicalValue (Q : BinaryQuadraticData V) : Module.Dual (ZMod 2) Q.radical :=
  { toFun := fun x ↦ Q.toFun x
    map_add' := fun x y ↦ by
      change Q.toFun ((x : V) + (y : V)) = Q.toFun (x : V) + Q.toFun (y : V)
      rw [Q.map_add_polar]
      have hy : Q.polarMap (y : V) = 0 := y.property
      rw [hy]
      simp
    map_smul' := fun a x ↦ by
      rcases binary_eq_zero_or_one a with rfl | rfl
      · simp [Q.map_zero]
      · simp }

/-- The finite affine space of linear repairs whose sum with the quadratic
function vanishes on the radical. -/
noncomputable def repairs (Q : BinaryQuadraticData V) [Fintype V] :
    Finset (Module.Dual (ZMod 2) V) := by
  classical
  letI : Fintype (Module.Dual (ZMod 2) V) :=
    Fintype.ofInjective (fun l : Module.Dual (ZMod 2) V ↦ (l : V → ZMod 2))
      DFunLike.coe_injective
  exact Finset.univ.filter fun l ↦ Q.radical.dualRestrict l = Q.radicalValue

/-- Membership means precisely that the repaired quadratic function vanishes
on every radical vector. -/
theorem mem_repairs_iff (Q : BinaryQuadraticData V) [Fintype V]
    (l : Module.Dual (ZMod 2) V) :
    l ∈ Q.repairs ↔ ∀ r : Q.radical, Q.toFun r + l r = 0 := by
  classical
  letI : Fintype (Module.Dual (ZMod 2) V) :=
    Fintype.ofInjective (fun l : Module.Dual (ZMod 2) V ↦ (l : V → ZMod 2))
      DFunLike.coe_injective
  rw [repairs, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h r
    have hr := LinearMap.congr_fun h r
    rw [Submodule.dualRestrict_apply,
      show Q.radicalValue r = Q.toFun (r : V) by rfl] at hr
    rw [hr, CharTwo.add_self_eq_zero]
  · intro h
    ext r
    rw [Submodule.dualRestrict_apply,
      show Q.radicalValue r = Q.toFun (r : V) by rfl]
    exact (CharTwo.add_eq_zero.mp (h r)).symm

/-- Translation by one lift identifies all repairs with the annihilator of
the radical. -/
noncomputable def repairsEquivDualAnnihilator (Q : BinaryQuadraticData V) :
    Q.radical.dualAnnihilator ≃
      {l : Module.Dual (ZMod 2) V // Q.radical.dualRestrict l = Q.radicalValue} :=
  { toFun := fun a ↦ ⟨Subspace.dualLift Q.radical Q.radicalValue + a, by
    rw [map_add]
    change Q.radical.dualRestrict
      ((Subspace.dualLift Q.radical) Q.radicalValue) +
        Q.radical.dualRestrict (a : Module.Dual (ZMod 2) V) = _
    rw [← LinearMap.comp_apply, Subspace.dualRestrict_comp_dualLift Q.radical]
    change Q.radicalValue + Q.radical.dualRestrict
      (a : Module.Dual (ZMod 2) V) = Q.radicalValue
    have ha : Q.radical.dualRestrict (a : Module.Dual (ZMod 2) V) = 0 := by
      rw [← LinearMap.mem_ker, Q.radical.dualRestrict_ker_eq_dualAnnihilator]
      exact a.property
    rw [ha, add_zero]⟩
    invFun := fun l ↦ ⟨l - Subspace.dualLift Q.radical Q.radicalValue, by
    rw [← Q.radical.dualRestrict_ker_eq_dualAnnihilator, LinearMap.mem_ker]
    change Q.radical.dualRestrict
      ((l : Module.Dual (ZMod 2) V) -
        (Subspace.dualLift Q.radical) Q.radicalValue) = 0
    rw [map_sub, ← LinearMap.comp_apply,
      Subspace.dualRestrict_comp_dualLift Q.radical]
    change Q.radical.dualRestrict (l : Module.Dual (ZMod 2) V) -
      Q.radicalValue = 0
    exact sub_eq_zero.mpr l.property⟩
    left_inv := fun a ↦ by
      apply Subtype.ext
      simp only [Subtype.coe_mk]
      abel
    right_inv := fun l ↦ by
      apply Subtype.ext
      simp only [Subtype.coe_mk]
      abel }

/-- If the polar rank is `2t`, exactly `2^(2t)` linear repairs vanish on the
radical. -/
theorem card_repairs_of_polarRank
    (Q : BinaryQuadraticData V) [Fintype V]
    (t : ℕ)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = 2 * t) :
    Q.repairs.card = 2 ^ (2 * t) := by
  classical
  letI : Fintype (Module.Dual (ZMod 2) V) :=
    Fintype.ofInjective (fun l : Module.Dual (ZMod 2) V ↦ (l : V → ZMod 2))
      DFunLike.coe_injective
  have hcard : Q.repairs.card = Nat.card Q.radical.dualAnnihilator := by
    rw [← Fintype.card_coe]
    let e₁ : {l // l ∈ Q.repairs} ≃
        {l : Module.Dual (ZMod 2) V // Q.radical.dualRestrict l = Q.radicalValue} :=
      Equiv.subtypeEquivRight (fun l ↦ mem_repairs_iff Q l |>.trans <| by
        constructor
        · intro h
          ext r
          rw [Submodule.dualRestrict_apply,
            show Q.radicalValue r = Q.toFun (r : V) by rfl]
          exact (CharTwo.add_eq_zero.mp (h r)).symm
        · intro h r
          have hr := LinearMap.congr_fun h r
          rw [Submodule.dualRestrict_apply,
            show Q.radicalValue r = Q.toFun (r : V) by rfl] at hr
          rw [hr, CharTwo.add_self_eq_zero])
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      (e₁.trans Q.repairsEquivDualAnnihilator.symm)
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2)]
  have hr := Q.polarMap.finrank_range_add_finrank_ker
  have ha := Subspace.finrank_add_finrank_dualAnnihilator_eq Q.radical
  change Module.finrank (ZMod 2) Q.radical +
      Module.finrank (ZMod 2) Q.radical.dualAnnihilator =
        Module.finrank (ZMod 2) V at ha
  unfold radical at ha
  rw [Nat.card_eq_fintype_card, ZMod.card]
  change 2 ^ Module.finrank (ZMod 2)
    (LinearMap.ker Q.polarMap).dualAnnihilator = 2 ^ (2 * t)
  congr 1
  omega

end BinaryQuadraticData
end BinaryFieldCounterexamples.Gold

namespace BinaryFieldCounterexamples.Gold
namespace BinaryQuadraticData

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The integral sign of a binary value. -/
def binarySign (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by norm_num [binarySign]

/-- Binary addition multiplies signs. -/
theorem binarySign_add (a b : ZMod 2) :
    binarySign (a + b) = binarySign a * binarySign b := by
  rcases binary_eq_zero_or_one a with rfl | rfl <;>
    rcases binary_eq_zero_or_one b with rfl | rfl
  all_goals simp [binarySign, CharTwo.add_self_eq_zero]

@[simp] theorem binarySign_mul_self (a : ZMod 2) : binarySign a * binarySign a = 1 := by
  rcases binary_eq_zero_or_one a with rfl | rfl <;> norm_num

/-- The integral Walsh sum of a binary-valued function. -/
def walshSum [Fintype V] (f : V → ZMod 2) : ℤ :=
  ∑ x : V, binarySign (f x)

/-- A nontrivial binary linear character sums to zero. -/
theorem sum_binarySign_linear_eq_zero [Fintype V]
    (l : Module.Dual (ZMod 2) V) (hl : l ≠ 0) :
    (∑ x : V, binarySign (l x)) = 0 := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, l y = 1 := by
    by_contra h
    push_neg at h
    apply hl
    ext x
    have hx := h x
    rcases binary_eq_zero_or_one (l x) with hz | ho
    · exact hz
    · exact (hx ho).elim
  have hshift := Equiv.sum_comp (Equiv.addRight y) (fun x : V ↦ binarySign (l x))
  have hneg : (∑ x : V, binarySign (l x)) = -∑ x : V, binarySign (l x) := by
    calc
      _ = ∑ x : V, binarySign (l (x + y)) := hshift.symm
      _ = ∑ x : V, -binarySign (l x) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_add, hy, binarySign_add, binarySign_one]
        ring
      _ = _ := by exact Finset.sum_neg_distrib _
  omega


end BinaryQuadraticData
end BinaryFieldCounterexamples.Gold

namespace BinaryFieldCounterexamples.Gold
namespace BinaryQuadraticData

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Adding a linear repair leaves the polar identity unchanged. -/
theorem repaired_add (Q : BinaryQuadraticData V)
    (l : Module.Dual (ZMod 2) V) (x y : V) :
    Q.toFun (x + y) + l (x + y) =
      (Q.toFun x + l x) + (Q.toFun y + l y) + Q.polarMap y x := by
  rw [Q.map_add_polar, map_add]
  ring

/-- Squaring the Walsh sum counts radical directions. This is the elementary
character-orthogonality proof, before taking either square root sign. -/
theorem walshSum_sq_of_mem_repairs [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V)
    (hl : l ∈ Q.repairs) :
    walshSum (fun x ↦ Q.toFun x + l x) ^ 2 =
      (Nat.card V : ℤ) * Nat.card Q.radical := by
  classical
  let f : V → ZMod 2 := fun x ↦ Q.toFun x + l x
  have hfadd (x y : V) : f (x + y) = f x + f y + Q.polarMap y x :=
    repaired_add Q l x y
  have hrad (y : V) (hy : Q.polarMap y = 0) : f y = 0 := by
    exact (mem_repairs_iff Q l).mp hl ⟨y, hy⟩
  have hconv (y : V) :
      (∑ x : V, binarySign (f x) * binarySign (f (x + y))) =
        if Q.polarMap y = 0 then (Nat.card V : ℤ) else 0 := by
    rw [show (∑ x : V, binarySign (f x) * binarySign (f (x + y))) =
        binarySign (f y) * ∑ x : V, binarySign (Q.polarMap y x) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hfadd,
        binarySign_add (f x + f y) (Q.polarMap y x),
        binarySign_add (f x) (f y)]
      calc
        binarySign (f x) *
            (binarySign (f x) * binarySign (f y) * binarySign (Q.polarMap y x)) =
          (binarySign (f x) * binarySign (f x)) *
            (binarySign (f y) * binarySign (Q.polarMap y x)) := by ring
        _ = _ := by rw [binarySign_mul_self, one_mul]]
    by_cases hy : Q.polarMap y = 0
    · rw [if_pos hy, hrad y hy, binarySign_zero, one_mul]
      simp [hy, Nat.card_eq_fintype_card]
    · rw [if_neg hy, sum_binarySign_linear_eq_zero (Q.polarMap y) hy, mul_zero]
  have hsquare : walshSum f ^ 2 =
      ∑ y : V, ∑ x : V, binarySign (f x) * binarySign (f (x + y)) := by
    rw [pow_two, walshSum, Finset.sum_mul]
    have hshifted :
        (∑ x : V, binarySign (f x) * ∑ y : V, binarySign (f y)) =
          ∑ x : V, ∑ y : V, binarySign (f x) * binarySign (f (x + y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      have h := (Equiv.sum_comp (Equiv.addRight x)
        (fun y : V ↦ binarySign (f x) * binarySign (f y))).symm
      change (∑ y : V, binarySign (f x) * binarySign (f y)) =
        ∑ y : V, binarySign (f x) * binarySign (f (y + x)) at h
      simpa only [add_comm] using h
    rw [hshifted, Finset.sum_comm]
  rw [hsquare]
  simp_rw [hconv]
  rw [show (∑ y : V, if Q.polarMap y = 0 then (Nat.card V : ℤ) else 0) =
      (Nat.card V : ℤ) * Nat.card Q.radical by
    rw [← Finset.sum_filter]
    have hc : (Finset.univ.filter fun y : V ↦ Q.polarMap y = 0).card =
        Nat.card Q.radical := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    ring]

end BinaryQuadraticData
end BinaryFieldCounterexamples.Gold

namespace BinaryFieldCounterexamples.Gold
namespace BinaryQuadraticData

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Number of zeros of a binary-valued function. -/
noncomputable def zeroCount [Fintype V] (f : V → ZMod 2) : ℕ :=
  Nat.card {x : V // f x = 0}

/-- Walsh sum equals zeros minus nonzeros. -/
theorem walshSum_eq_two_mul_zeroCount_sub [Fintype V] (f : V → ZMod 2) :
    walshSum f = 2 * (zeroCount f : ℤ) - Nat.card V := by
  classical
  rw [walshSum, zeroCount]
  have hpoint (x : V) : binarySign (f x) =
      2 * (if f x = 0 then (1 : ℤ) else 0) - 1 := by
    by_cases hx : f x = 0 <;> simp [binarySign, hx]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (2 : ℤ) * (∑ x ∈ (Finset.univ : Finset V),
    if f x = 0 then 1 else 0) - (∑ x : V, (1 : ℤ)) = _
  rw [Finset.sum_boole]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]
  congr 2
  norm_cast
  rw [Fintype.card_subtype]

/-- Exact radical cardinality from the polar rank. -/
theorem card_radical_of_polarRank [Fintype V]
    (Q : BinaryQuadraticData V) (r : ℕ)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = r) :
    Nat.card Q.radical = Nat.card V / 2 ^ r := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)]
  rw [show Nat.card (ZMod 2) = 2 by
    rw [Nat.card_eq_fintype_card, ZMod.card]]
  have hr := Q.polarMap.finrank_range_add_finrank_ker
  have hrle : r ≤ Module.finrank (ZMod 2) V := by omega
  unfold radical
  change 2 ^ Module.finrank (ZMod 2) (LinearMap.ker Q.polarMap) = _
  have hk : Module.finrank (ZMod 2) (LinearMap.ker Q.polarMap) =
      Module.finrank (ZMod 2) V - r := by omega
  rw [hk, Nat.pow_div hrle (by decide : 0 < 2)]

/-- At polar rank `2t`, every repair has one of the two classical Walsh
signs, with absolute value `2^(d-t)`. -/
theorem walshSum_eq_sign_of_polarRank [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V)
    (hl : l ∈ Q.repairs) (d t : ℕ)
    (hdim : Module.finrank (ZMod 2) V = d)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = 2 * t) :
    walshSum (fun x ↦ Q.toFun x + l x) = (2 ^ (d - t) : ℕ) ∨
      walshSum (fun x ↦ Q.toFun x + l x) = -(2 ^ (d - t) : ℕ) := by
  have hrt := Q.polarMap.finrank_range_add_finrank_ker
  have hle : 2 * t ≤ d := by omega
  have hrad := card_radical_of_polarRank Q (2 * t) hrank
  have hV : Nat.card V = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hdim,
      Nat.card_eq_fintype_card, ZMod.card]
  have hrad' : Nat.card Q.radical = 2 ^ (d - 2 * t) := by
    rw [hrad, hV, Nat.pow_div hle (by decide : 0 < 2)]
  have hs := walshSum_sq_of_mem_repairs Q l hl
  rw [hV, hrad'] at hs
  have hexp : d + (d - 2 * t) = 2 * (d - t) := by omega
  have hs' : walshSum (fun x ↦ Q.toFun x + l x) ^ 2 =
      ((2 ^ (d - t) : ℕ) : ℤ) ^ 2 := by
    calc
      _ = ((2 ^ d : ℕ) : ℤ) * ((2 ^ (d - 2 * t) : ℕ) : ℤ) := hs
      _ = ((2 ^ (d + (d - 2 * t)) : ℕ) : ℤ) := by
        norm_cast
        rw [pow_add]
      _ = ((2 ^ (d - t) : ℕ) : ℤ) ^ 2 := by
        rw [hexp, mul_comm 2 (d - t), pow_mul]
        norm_cast
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hs'

end BinaryQuadraticData
end BinaryFieldCounterexamples.Gold

namespace BinaryFieldCounterexamples.Gold
namespace BinaryQuadraticData

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Adding the constant bit flips the Walsh sign. -/
theorem walshSum_add_one [Fintype V] (f : V → ZMod 2) :
    walshSum (fun x ↦ f x + 1) = -walshSum f := by
  classical
  rw [walshSum, walshSum]
  simp_rw [binarySign_add, binarySign_one]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Every radical-compatible repair has a unique choice of constant sign with
the majority zero count used in the Gold construction. -/
theorem exists_bit_zeroCount_of_polarRank [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V)
    (hl : l ∈ Q.repairs) (d t : ℕ) (ht : 1 ≤ t)
    (hdim : Module.finrank (ZMod 2) V = d)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) = 2 * t) :
    ∃! κ : ZMod 2,
      zeroCount (fun x ↦ Q.toFun x + l x + κ) =
        2 ^ (d - 1) + 2 ^ (d - t - 1) := by
  let f : V → ZMod 2 := fun x ↦ Q.toFun x + l x
  have hrt := Q.polarMap.finrank_range_add_finrank_ker
  have hle : 2 * t ≤ d := by omega
  have hdpos : 1 ≤ d := by omega
  have hdtpos : 1 ≤ d - t := by omega
  have hV : Nat.card V = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hdim,
      Nat.card_eq_fintype_card, ZMod.card]
  have hsign := walshSum_eq_sign_of_polarRank Q l hl d t hdim hrank
  have htarget (g : V → ZMod 2)
      (hw : walshSum g = (2 ^ (d - t) : ℕ)) :
      zeroCount g = 2 ^ (d - 1) + 2 ^ (d - t - 1) := by
    have hc := walshSum_eq_two_mul_zeroCount_sub g
    rw [hw, hV] at hc
    have hd : 2 ^ d = 2 * 2 ^ (d - 1) := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_add]
      ring
    have hdt : 2 ^ (d - t) = 2 * 2 ^ (d - t - 1) := by
      conv_lhs => rw [show d - t = (d - t - 1) + 1 by omega, pow_add]
      ring
    rw [hd, hdt] at hc
    omega
  rcases hsign with hpos | hneg
  · refine ⟨0, ?_, ?_⟩
    · simpa only [add_zero] using htarget f hpos
    · intro κ hκ
      rcases binary_eq_zero_or_one κ with rfl | rfl
      · rfl
      · exfalso
        have hflip := walshSum_add_one f
        have hcount := walshSum_eq_two_mul_zeroCount_sub (fun x ↦ f x + 1)
        rw [hflip, hpos, hκ, hV] at hcount
        have hd : 2 ^ d = 2 * 2 ^ (d - 1) := by
          conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_add]
          ring
        have hdt : 2 ^ (d - t) = 2 * 2 ^ (d - t - 1) := by
          conv_lhs => rw [show d - t = (d - t - 1) + 1 by omega, pow_add]
          ring
        rw [hd, hdt] at hcount
        have hp : 0 < 2 ^ (d - t - 1) := pow_pos (by decide) _
        omega
  · refine ⟨1, ?_, ?_⟩
    · apply htarget (fun x ↦ f x + 1)
      rw [walshSum_add_one, hneg, neg_neg]
    · intro κ hκ
      rcases binary_eq_zero_or_one κ with rfl | rfl
      · exfalso
        have hcount := walshSum_eq_two_mul_zeroCount_sub f
        have hκ' : zeroCount f = 2 ^ (d - 1) + 2 ^ (d - t - 1) := by
          simpa only [f, add_zero] using hκ
        rw [hneg, hκ', hV] at hcount
        have hd : 2 ^ d = 2 * 2 ^ (d - 1) := by
          conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_add]
          ring
        have hdt : 2 ^ (d - t) = 2 * 2 ^ (d - t - 1) := by
          conv_lhs => rw [show d - t = (d - t - 1) + 1 by omega, pow_add]
          ring
        rw [hd, hdt] at hcount
        have hp : 0 < 2 ^ (d - t - 1) := pow_pos (by decide) _
        omega
      · rfl

end BinaryQuadraticData
end BinaryFieldCounterexamples.Gold
