/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Counting.GaussianIdentities
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The integral quadratic-form list size

The rational expression in the main theorem is the cast of an explicit natural
number, allowing an exact-size locator subfamily before collision averaging.
-/

@[expose] public section

namespace BinaryFieldCounterexamples
open scoped BigOperators

/-- The rational list-size expression is the cast of an explicit natural number. -/
def quadraticListCount (b n h t : ℕ) : ℕ :=
  b^(2*t)*(∑ i∈Finset.range t,b^i)*gaussianPascal (b^2) (n-h) t

/-- Exact integrality of the quadratic-form list size. -/
theorem quadratic_list_size_eq_natCast (b n h t : ℕ) (hb : 2≤b) (ht : t≤n-h) :
    (b:ℚ)^(2*t)*((b:ℚ)^t-1)*quadraticGaussian (b^2) (n-h) t/(b-1) =
      (quadraticListCount b n h t:ℚ) := by
  rw [quadraticGaussian_eq_gaussianPascal (b^2) (n-h) t
    (Nat.one_lt_pow (by omega) (by omega)) ht]
  have hb1 : (b:ℚ)-1≠0 := by
    have : (b:ℚ)≠1 := by exact_mod_cast (show b≠1 by omega)
    exact sub_ne_zero.mpr this
  rw [div_eq_iff hb1]
  simp only [quadraticListCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum]
  have hg := geom_sum_mul (b:ℚ) t
  rw [←hg]
  ring

/-- The integral quadratic-form list size is nonzero throughout the theorem's
parameter range. -/
theorem quadraticListCount_pos (b n h t : ℕ) (hb : 2≤b) (ht0 : 1≤t)
    (ht : t≤n-h) : 0<quadraticListCount b n h t := by
  have hpositive : ∀N j : ℕ,j≤N→0<gaussianPascal (b^2) N j := by
    intro N
    induction N with
    | zero =>
        intro j hj
        have : j=0 := by omega
        subst j
        simp [gaussianPascal]
    | succ N ih =>
        intro j hj
        cases j with
        | zero => simp [gaussianPascal]
        | succ j =>
            by_cases hle : j≤N
            · rw [gaussianPascal_succ]
              exact Nat.add_pos_left (ih j hle) _
            · have heq : j=N := by omega
              subst j
              simp [gaussianPascal_self]
  have hgauss : 0<gaussianPascal (b^2) (n-h) t := hpositive (n-h) t ht
  have hsum : 0<∑i∈Finset.range t,b^i := by
    have hzero : 0∈Finset.range t := Finset.mem_range.mpr (by omega)
    have hone : 1≤∑i∈Finset.range t,b^i := by
      simpa using Finset.single_le_sum (fun i _ => Nat.zero_le (b^i)) hzero
    omega
  simp only [quadraticListCount]
  positivity

end BinaryFieldCounterexamples
