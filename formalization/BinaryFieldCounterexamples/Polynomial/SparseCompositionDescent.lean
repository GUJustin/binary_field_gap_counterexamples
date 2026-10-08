/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QLinearizedDescent
public import BinaryFieldCounterexamples.Polynomial.SimpleRootComposition
/-!
# Recovering both ends of sparse support under composition

For a degree-q linearized inner polynomial with nonzero linear coefficient,
composition preserves the lower nonconstant support threshold and increases
the largest Frobenius index by one. This theorem combines literal support
recovery, simple-root divisibility, and exact degree multiplication.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.FiniteFieldLocator
open Polynomial
variable {k K : Type*} [Field k] [Fintype k] [Field K] [Algebra k K]
set_option maxHeartbeats 1000000

/-- Recover the entire allowed Frobenius-index interval of the outer
polynomial from its composite, leaving the constant coefficient unrestricted. -/
theorem support_interval_of_comp (A H : K[X]) (t u : ℕ)
    (hA : IsQLinearized (k := k) A) (hdegree : A.natDegree = Fintype.card k)
    (hderiv : A.derivative.eval 0 ≠ 0)
    (hcomp : IsQLinearized (k := k) (H.comp A - C ((H.comp A).coeff 0)))
    (hlow : X^((Fintype.card k)^t) ∣ H.comp A - C ((H.comp A).coeff 0))
    (hhigh : (H.comp A).natDegree ≤ (Fintype.card k)^(u+1)) :
    ∀ e ∈ H.support, e = 0 ∨ ∃ i : ℕ, t ≤ i ∧ i ≤ u ∧ e = (Fintype.card k)^i := by
  have hz : A.eval 0 = 0 := by rw [← coeff_zero_eq_eval_zero]; exact hA.coeff_zero A
  have hc : (H.comp A).coeff 0 = H.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp, hz, ← coeff_zero_eq_eval_zero]
  have hs := isQLinearized_sub_constant_of_comp A H hA hdegree hcomp
  have hl : X^((Fintype.card k)^t) ∣ H-C (H.coeff 0) := by
    apply (X_pow_dvd_comp_simple_zero A _ hz hderiv _).mp
    simpa only [sub_comp, C_comp, hc] using hlow
  intro e he
  by_cases he0 : e = 0
  · exact Or.inl he0
  have he' : e ∈ (H-C (H.coeff 0)).support := by
    simpa only [mem_support_iff, coeff_sub, coeff_C, ite_eq_right he0, sub_zero] using he
  obtain ⟨i, hi⟩ := hs e he'
  refine Or.inr ⟨i, ?_, ?_, hi⟩
  · apply (Nat.pow_le_pow_iff_right (Fintype.one_lt_card : 1 < Fintype.card k)).mp
    rw [← hi]
    by_contra hn
    have hez := X_pow_dvd_iff.mp hl e (by omega)
    exact (mem_support_iff.mp he') hez
  · apply Nat.le_of_succ_le_succ
    apply (Nat.pow_le_pow_iff_right (Fintype.one_lt_card : 1 < Fintype.card k)).mp
    rw [pow_succ]
    calc
      (Fintype.card k)^i * Fintype.card k ≤ H.natDegree * Fintype.card k :=
        Nat.mul_le_mul_right _ (hi ▸ le_natDegree_of_mem_supp e he)
      _ ≤ (Fintype.card k)^(u+1) := by simpa only [natDegree_comp, hdegree] using hhigh
end BinaryFieldCounterexamples.FiniteFieldLocator
