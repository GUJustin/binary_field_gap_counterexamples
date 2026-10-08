/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.QuadraticCharacters
/-!
# Binary characters and positive Fourier expansions on linear codes

Summing a binary character over an actual submodule gives its cardinality or
zero. Consequently a nonnegative character expansion has code average at least
its zero-character coefficient. The Gold rank-population argument will use this
with an explicitly proved Gaussian rank-weight expansion; that separate finite
character identity is not assumed available by this module.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
open Gold.BinaryQuadraticData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
/-- Orthogonality on the actual code, including the trivial restricted character. -/
theorem sum_binarySign_submodule (C : Submodule (ZMod 2) V) [Fintype C]
    (l : Module.Dual (ZMod 2) V) :
    (∑ x : C, binarySign (l x)) =
      if l.comp C.subtype=0 then (Nat.card C : ℤ) else 0 := by
  classical
  split_ifs with h
  · have hz : ∀ x : C, l x=0 := fun x => LinearMap.congr_fun h x
    simp [hz, Nat.card_eq_fintype_card]
  · exact sum_binarySign_linear_eq_zero (l.comp C.subtype) h

/-- Every binary character has a nonnegative sum on a linear code. -/
theorem sum_binarySign_submodule_nonneg (C : Submodule (ZMod 2) V) [Fintype C]
    (l : Module.Dual (ZMod 2) V) :
    (0 : ℤ) ≤ ∑ x : C, binarySign (l x) := by
  rw [sum_binarySign_submodule]
  split_ifs <;> positivity

/-- A proved nonnegative finite character expansion gives a lower bound from its
zero-character term, without an association-scheme axiom. -/
theorem sum_nonneg_character_expansion_lower_bound
    [Fintype (Module.Dual (ZMod 2) V)]
    (C : Submodule (ZMod 2) V) [Fintype C] (f : V → ℚ)
    (w : Module.Dual (ZMod 2) V → ℚ)
    (hw : ∀ l, 0 ≤ w l)
    (hf : ∀ x, f x=∑ l, w l*(binarySign (l x) : ℚ)) :
    (Nat.card C : ℚ)*w 0 ≤ ∑ x : C, f x := by
  classical
  simp_rw [hf]
  rw [Finset.sum_comm]
  have hs : ∀ l : Module.Dual (ZMod 2) V,
      (∑ x : C, w l*(binarySign (l x) : ℚ)) =
        w l * ((∑ x : C, binarySign (l x) : ℤ) : ℚ) := by
    intro l
    simp [Finset.mul_sum]
  simp_rw [hs]
  have hn : ∀ l : Module.Dual (ZMod 2) V,
      0 ≤ w l * ((∑ x : C, binarySign (l x) : ℤ) : ℚ) := by
    intro l
    exact mul_nonneg (hw l) (by exact_mod_cast sum_binarySign_submodule_nonneg C l)
  have hb := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hn l)
    (Finset.mem_univ (0 : Module.Dual (ZMod 2) V))
  simpa [Nat.card_eq_fintype_card, mul_comm] using hb
end BinaryFieldCounterexamples
