/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.PrimePowerSupport
public import Mathlib.Algebra.Polynomial.EraseLead
/-!
# Recovering prime-power support under composition

For a scalar-linearized polynomial of exact degree q, composition cannot hide
non-q-power exponents in the outer polynomial. The proof removes its leading
term and inducts on degree. The same statement holds after subtracting the
constant term, as needed for translated quadratic derivatives.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.FiniteFieldLocator
open Polynomial
variable {k K : Type*} [Field k] [Fintype k] [Field K] [Algebra k K]
set_option maxHeartbeats 1000000

/-- Iterated scalar Frobenius preserves literal q-power support. -/
theorem IsQLinearized.pow_card_power (A : K[X]) (hA : IsQLinearized (k := k) A) (i : ℕ) :
    IsQLinearized (k := k) (A ^ (Fintype.card k)^i) := by
  induction i with
  | zero => simpa using hA
  | succ i ih =>
    rw [pow_succ, pow_mul]
    exact ih.pow_card _

/-- If composition through a q-linearized polynomial of degree q has q-power support, then the outer polynomial itself has q-power support. -/
theorem isQLinearized_of_comp (A H : K[X]) (hA : IsQLinearized (k := k) A)
    (hdegree : A.natDegree = Fintype.card k)
    (hcomp : IsQLinearized (k := k) (H.comp A)) : IsQLinearized (k := k) H := by
  classical
  have hzero : IsQLinearized (k := k) (0 : K[X]) := by simp [IsQLinearized]
  induction hn : H.natDegree using Nat.strong_induction_on generalizing H with
  | h n ih =>
    by_cases hH : H = 0
    · simpa [hH] using hzero
    have hA0 : A.natDegree ≠ 0 := by rw [hdegree]; exact Fintype.card_ne_zero
    have hc0 : H.comp A ≠ 0 := by
      intro hz
      rcases comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
      · exact hH h
      · exact hA0 (by rw [h, natDegree_C])
    obtain ⟨i, hi⟩ := hcomp _ (natDegree_mem_support_of_nonzero hc0)
    rw [natDegree_comp, hdegree] at hi
    have hi0 : i ≠ 0 := by
      intro hz
      rw [hz, pow_zero] at hi
      have := Fintype.one_lt_card (α := k)
      have hm := Nat.eq_one_of_dvd_one (show Fintype.card k ∣ 1 from ⟨H.natDegree, by simpa [Nat.mul_comm] using hi.symm⟩)
      omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rw [pow_succ] at hi
    have hdeg : H.natDegree = (Fintype.card k)^j := Nat.eq_of_mul_eq_mul_right Fintype.card_pos hi
    have hm : IsQLinearized (k := k) ((C H.leadingCoeff * X^H.natDegree).comp A) := by
      rw [mul_comp, C_comp, pow_comp, X_comp, hdeg]
      exact (hA.pow_card_power A j).c_mul _ _
    have hec : IsQLinearized (k := k) (H.eraseLead.comp A) := by
      have he := H.eraseLead_add_C_mul_X_pow
      have he' : H.eraseLead = H - C H.leadingCoeff * X^H.natDegree := eq_sub_of_add_eq he
      rw [he', sub_comp]
      exact hcomp.sub _ _ hm
    have he : IsQLinearized (k := k) H.eraseLead := by
      rcases H.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hz
      · exact ih H.eraseLead.natDegree (by omega) H.eraseLead hec rfl
      · simpa [hz] using hzero
    intro e hem
    by_cases heq : e = H.natDegree
    · exact ⟨j, heq.trans hdeg⟩
    · apply he e
      simpa only [eraseLead_support, Finset.mem_erase, ne_eq] using And.intro heq hem
/-- The inverse support statement also holds after subtracting constant terms. -/
theorem isQLinearized_sub_constant_of_comp (A H : K[X])
    (hA : IsQLinearized (k := k) A) (hdegree : A.natDegree = Fintype.card k)
    (hcomp : IsQLinearized (k := k) (H.comp A - C ((H.comp A).coeff 0))) :
    IsQLinearized (k := k) (H - C (H.coeff 0)) := by
  apply isQLinearized_of_comp A _ hA hdegree
  rw [sub_comp, C_comp]
  have he : (H.comp A).coeff 0 = H.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero,
      hA.coeff_zero A, ← coeff_zero_eq_eval_zero]
  rwa [he] at hcomp
end BinaryFieldCounterexamples.FiniteFieldLocator
