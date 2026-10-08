/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import ArkLib.ToMathlib.Finset.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Reciprocal agreement outside the pole

The second input `x ↦ 1 / (x - β)` agrees with any polynomial of degree strictly
less than `k` at at most `k` domain points, provided `β` is outside the domain.
This is the upper-bound step for the second input in the paper's pole reduction.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

open Polynomial

/-- The second input `1 / (x - β)` on a domain avoiding its pole has at most `k` agreements
with a polynomial of degree strictly less than `k`. The statement includes `k = 0`. -/
theorem reciprocal_agreement_card_le
    {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (β : F) (hβ : β ∉ D) (P : F[X]) (k : ℕ)
    (hP : P.degree < k) :
    (D.filter fun x ↦ P.eval x = (x - β)⁻¹).card ≤ k := by
  let R : F[X] := (X - C β) * P - 1
  have hR : R ≠ 0 := by
    intro h
    have := congrArg (fun Q : F[X] ↦ Q.eval β) h
    simp [R] at this
  have hdegree : R.natDegree ≤ k := by
    by_cases hp : P = 0
    · simp [R, hp]
    · have hd : P.natDegree < k := (natDegree_lt_iff_degree_lt hp).mpr hP
      calc
        R.natDegree ≤ max ((X - C β) * P).natDegree (1 : F[X]).natDegree :=
          natDegree_sub_le _ _
        _ ≤ k := by
          simp only [natDegree_one, max_zero]
          calc
            ((X - C β) * P).natDegree ≤ (X - C β).natDegree + P.natDegree :=
              natDegree_mul_le
            _ ≤ k := by rw [natDegree_X_sub_C]; omega
  have hroots : (D.filter fun x ↦ P.eval x = (x - β)⁻¹) ⊆ R.roots.toFinset := by
    intro x hx
    obtain ⟨hxD, hxP⟩ := Finset.mem_filter.mp hx
    have hxβ : x - β ≠ 0 := sub_ne_zero.mpr (fun h ↦ hβ (h ▸ hxD))
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hR).mpr
    simp [R, hxP, hxβ]
  exact (Finset.card_le_card hroots).trans
    ((Multiset.toFinset_card_le _).trans ((card_roots' R).trans hdegree))

end BinaryFieldCounterexamples
