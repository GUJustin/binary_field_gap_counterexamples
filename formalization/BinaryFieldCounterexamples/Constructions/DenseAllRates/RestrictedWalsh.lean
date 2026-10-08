/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.DenseAllRates.TraceRank
public import BinaryFieldCounterexamples.Constructions.Gold.QuadraticCharacters

/-!
# Walsh bounds on affine restrictions

Binary quadratic data restricts to linear subspaces and affine translates with
the expected polar map.  Character orthogonality gives an exact zero-or-square
alternative for arbitrary linear repairs and constants, hence the standard
absolute Walsh bound from a polar-rank lower bound.
-/

@[expose] public section

namespace BinaryFieldCounterexamples.Gold
namespace BinaryQuadraticData
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Restriction of actual binary quadratic data to a linear subspace. -/
def restrict (Q : BinaryQuadraticData V) (W : Submodule (ZMod 2) V) :
    BinaryQuadraticData W :=
  BinaryQuadraticData.mk (fun x ↦ Q.toFun x)
    (Gold.restrictPolarMap W Q.polarMap) (by simp [Q.map_zero]) (by
      intro x y
      exact Q.map_add_polar x y)

@[simp] theorem restrict_toFun (Q : BinaryQuadraticData V)
    (W : Submodule (ZMod 2) V) (x : W) :
    (Q.restrict W).toFun x = Q.toFun x := by rfl

@[simp] theorem restrict_polarMap_apply (Q : BinaryQuadraticData V)
    (W : Submodule (ZMod 2) V) (x y : W) :
    (Q.restrict W).polarMap x y = Q.polarMap x y := by rfl

/-- Normalized restriction to the affine translate `a + W`.  Adding back the
constant `Q(a)` recovers the literal translated quadratic function. -/
def affineRestrict (Q : BinaryQuadraticData V) (W : Submodule (ZMod 2) V)
    (a : V) : BinaryQuadraticData W :=
  BinaryQuadraticData.mk
    (fun x ↦ Q.toFun x + Q.polarMap a x)
    (Gold.restrictPolarMap W Q.polarMap) (by simp [Q.map_zero]) (by
      intro x y
      change Q.toFun ((x : V) + (y : V)) +
          Q.polarMap a ((x : V) + (y : V)) =
        (Q.toFun x + Q.polarMap a x) +
          (Q.toFun y + Q.polarMap a y) + Q.polarMap y x
      rw [Q.map_add_polar, map_add]
      ring)

/-- The normalized affine restriction is literal translation by `a`, followed
by addition of the constant `Q(a)`. -/
theorem affineRestrict_toFun (Q : BinaryQuadraticData V)
    (W : Submodule (ZMod 2) V) (a : V) (x : W) :
    (Q.affineRestrict W a).toFun x = Q.toFun ((x : V) + a) + Q.toFun a := by
  rw [Q.map_add_polar]
  change Q.toFun x + Q.polarMap a x =
    Q.toFun x + Q.toFun a + Q.polarMap a x + Q.toFun a
  have ha : Q.toFun a + Q.toFun a = 0 := CharTwo.add_self_eq_zero _
  symm
  calc
    Q.toFun x + Q.toFun a + Q.polarMap a x + Q.toFun a =
        Q.toFun x + Q.polarMap a x + (Q.toFun a + Q.toFun a) := by ring
    _ = Q.toFun x + Q.polarMap a x := by rw [ha, add_zero]

@[simp] theorem affineRestrict_polarMap_apply (Q : BinaryQuadraticData V)
    (W : Submodule (ZMod 2) V) (a : V) (x y : W) :
    (Q.affineRestrict W a).polarMap x y = Q.polarMap x y := by rfl

/-- The exact Walsh alternative for an arbitrary linear perturbation: either
it is incompatible with the radical and the sum vanishes, or its square is the
standard radical cardinality. -/
theorem walshSum_zero_or_sq_eq [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V) :
    walshSum (fun x ↦ Q.toFun x + l x) = 0 ∨
      walshSum (fun x ↦ Q.toFun x + l x) ^ 2 =
        (Nat.card V : ℤ) * Nat.card Q.radical := by
  classical
  by_cases hl : l ∈ Q.repairs
  · exact Or.inr (walshSum_sq_of_mem_repairs Q l hl)
  · left
    rw [mem_repairs_iff] at hl
    push Not at hl
    obtain ⟨r, hr⟩ := hl
    have hfr : Q.toFun r + l r = 1 := by
      rcases binary_eq_zero_or_one (Q.toFun r + l r) with hz | ho
      · exact (hr hz).elim
      · exact ho
    let f : V → ZMod 2 := fun x ↦ Q.toFun x + l x
    have hshift := Equiv.sum_comp (Equiv.addRight (r : V))
      (fun x : V ↦ binarySign (f x))
    have hneg : walshSum f = -walshSum f := by
      rw [walshSum]
      calc
        (∑ x : V, binarySign (f x)) =
            ∑ x : V, binarySign (f (x + r)) := hshift.symm
        _ = ∑ x : V, -binarySign (f x) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hrmap : Q.polarMap (r : V) = 0 := r.property
          have hrpolar : Q.polarMap (r : V) x = 0 := by rw [hrmap]; rfl
          have hf : f (x + r) = f x + 1 := by
            dsimp only [f]
            rw [Q.map_add_polar, map_add, hrpolar, add_zero]
            calc
              Q.toFun x + Q.toFun r + (l x + l r) =
                  (Q.toFun x + l x) + (Q.toFun r + l r) := by ring
              _ = Q.toFun x + l x + 1 := by rw [hfr]
          rw [hf, binarySign_add, binarySign_one]
          ring
        _ = -∑ x : V, binarySign (f x) := by rw [Finset.sum_neg_distrib]
    dsimp only [f] at hneg
    rw [walshSum] at hneg ⊢
    omega

/-- An added constant bit does not change the square of a Walsh sum. -/
theorem walshSum_add_const_sq [Fintype V]
    (f : V → ZMod 2) (κ : ZMod 2) :
    walshSum (fun x ↦ f x + κ) ^ 2 = walshSum f ^ 2 := by
  rcases binary_eq_zero_or_one κ with rfl | rfl
  · simp
  · rw [walshSum_add_one]
    ring

/-- Arbitrary linear and constant perturbations obey the radical-square upper
bound. -/
theorem walshSum_linear_const_sq_le [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V) (κ : ZMod 2) :
    walshSum (fun x ↦ Q.toFun x + l x + κ) ^ 2 ≤
      (Nat.card V : ℤ) * Nat.card Q.radical := by
  rw [show (fun x ↦ Q.toFun x + l x + κ) =
      (fun x ↦ (Q.toFun x + l x) + κ) by rfl,
    walshSum_add_const_sq]
  rcases walshSum_zero_or_sq_eq Q l with hz | heq
  · rw [hz]
    positivity
  · rw [heq]

/-- A rank lower bound gives the usual absolute Walsh bound, uniformly
for every linear and constant perturbation. -/
theorem abs_walshSum_linear_const_le_of_rank [Fintype V]
    (Q : BinaryQuadraticData V) (l : Module.Dual (ZMod 2) V) (κ : ZMod 2)
    (d t : ℕ) (hdim : Module.finrank (ZMod 2) V = d)
    (hrank : 2 * t ≤ Module.finrank (ZMod 2) (LinearMap.range Q.polarMap)) :
    |walshSum (fun x ↦ Q.toFun x + l x + κ)| ≤ ((2 ^ (d - t) : ℕ) : ℤ) := by
  have hnull := Q.polarMap.finrank_range_add_finrank_ker
  have hdt : 2 * t ≤ d := by omega
  have hk : Module.finrank (ZMod 2) Q.radical ≤ d - 2 * t := by
    unfold radical
    omega
  have hV : Nat.card V = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hdim,
      Nat.card_eq_fintype_card, ZMod.card]
  have hR : Nat.card Q.radical =
      2 ^ Module.finrank (ZMod 2) Q.radical := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_eq_fintype_card, ZMod.card]
  have hexp : d + Module.finrank (ZMod 2) Q.radical ≤ 2 * (d - t) := by omega
  have hs := walshSum_linear_const_sq_le Q l κ
  rw [hV, hR] at hs
  have hs' : walshSum (fun x ↦ Q.toFun x + l x + κ) ^ 2 ≤
      (((2 ^ (d - t) : ℕ) : ℤ)) ^ 2 := by
    calc
      _ ≤ ((2 ^ d : ℕ) : ℤ) *
          ((2 ^ Module.finrank (ZMod 2) Q.radical : ℕ) : ℤ) := hs
      _ = ((2 ^ (d + Module.finrank (ZMod 2) Q.radical) : ℕ) : ℤ) := by
        norm_cast
        rw [pow_add]
      _ ≤ ((2 ^ (2 * (d - t)) : ℕ) : ℤ) := by
        exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hexp
      _ = (((2 ^ (d - t) : ℕ) : ℤ)) ^ 2 := by
        rw [show 2 * (d - t) = (d - t) * 2 by omega, pow_mul]
        norm_cast
  exact abs_le_of_sq_le_sq hs' (by positivity)

/-- Restriction to codimension at most `c` lowers the actual polar rank by at
most `2c`. -/
theorem polar_rank_le_restrict_add_two_codim [FiniteDimensional (ZMod 2) V]
    (Q : BinaryQuadraticData V) (W : Submodule (ZMod 2) V) (c : ℕ)
    (hcodim : Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) W + c) :
    Module.finrank (ZMod 2) (LinearMap.range Q.polarMap) ≤
      Module.finrank (ZMod 2) (LinearMap.range (Q.restrict W).polarMap) + 2*c := by
  exact Gold.polar_rank_le_restriction_add_two_codim W Q.polarMap c hcodim

end BinaryQuadraticData
end BinaryFieldCounterexamples.Gold
