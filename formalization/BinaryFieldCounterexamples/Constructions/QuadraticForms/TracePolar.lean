/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TracePolynomial
public import Mathlib.RingTheory.Trace.Basic
/-!
# The polar trace identity for the concrete quadratic family

The cyclic and middle half-trace blocks have polar form given by the field
trace pairing with their literal polynomial derivative. Nondegeneracy then
identifies the actual polar radical with the derivative zero set. These
identities apply in every characteristic, including characteristic two.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Scalar-field Frobenius powers preserve the actual field trace. -/
theorem trace_frobenius_power (r : ℕ) (x : B) :
    Algebra.trace k B (x^((Fintype.card k)^r)) = Algebra.trace k B x := by
  induction r with
  | zero => simp
  | succ r hr =>
    have h := Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic k B)
      (x^((Fintype.card k)^r))
    change Algebra.trace k B ((x^((Fintype.card k)^r))^(Fintype.card k)) = _ at h
    rw [Nat.pow_succ, pow_mul]
    exact h.trans hr

/-- Frobenius powers are additive over the scalar finite field. -/
theorem scalar_frobenius_add (r : ℕ) (x y : B) :
    (x+y)^((Fintype.card k)^r) = x^((Fintype.card k)^r)+y^((Fintype.card k)^r) := by
  simpa only [FiniteFieldLocator.qPowerLinearMap_apply] using
    (FiniteFieldLocator.qPowerLinearMap (k:=k) r).map_add x y

/-- Frobenius conjugation transfers one factor to the other side of the trace pairing. -/
theorem trace_frobenius_transfer (m i : ℕ) (hi : i ≤ m)
    (hcard : Fintype.card B = (Fintype.card k)^m) (a x y : B) :
    Algebra.trace k B (a*x*y^((Fintype.card k)^i)) =
      Algebra.trace k B (a^((Fintype.card k)^(m-i))*x^((Fintype.card k)^(m-i))*y) := by
  have h := trace_frobenius_power (k:=k) (m-i) (a*x*y^((Fintype.card k)^i))
  rw [mul_pow,mul_pow,← pow_mul,← Nat.pow_add,Nat.add_sub_of_le hi,← hcard,
    FiniteField.pow_card] at h
  exact h.symm

/-- A full cyclic trace block has the trace pairing with its literal derivative as polar form. -/
theorem cyclicTracePolynomial_polar (m i : ℕ) (hi : 0 < i) (him : i < m)
    (hcard : Fintype.card B = (Fintype.card k)^m) (a x y : B) :
    (cyclicTracePolynomial (k:=k) m i a).eval (x+y) -
      (cyclicTracePolynomial (k:=k) m i a).eval x -
      (cyclicTracePolynomial (k:=k) m i a).eval y =
    algebraMap k B (Algebra.trace k B
      (y*(cyclicTracePolynomial (k:=k) m i a).derivative.eval x)) := by
  rw [cyclicTracePolynomial_eval_trace _ _ _ _ hcard,
    cyclicTracePolynomial_eval_trace _ _ _ _ hcard,
    cyclicTracePolynomial_eval_trace _ _ _ _ hcard,
    cyclicTracePolynomial_derivative _ _ hi him]
  simp only [eval_add,eval_mul,eval_C,eval_pow,eval_X]
  have hexp : a*(x+y)^((Fintype.card k)^i+1) =
      a*x^((Fintype.card k)^i+1)+a*y^((Fintype.card k)^i+1)+
        (a*x^((Fintype.card k)^i)*y+a*x*y^((Fintype.card k)^i)) := by
    simp only [pow_succ,scalar_frobenius_add (k:=k)]
    ring
  rw [hexp]
  simp only [map_add]
  rw [trace_frobenius_transfer m i (Nat.le_of_lt him) hcard]
  have he : y*(a*x^((Fintype.card k)^i)+
      a^((Fintype.card k)^(m-i))*x^((Fintype.card k)^(m-i))) =
      a*x^((Fintype.card k)^i)*y+
        a^((Fintype.card k)^(m-i))*x^((Fintype.card k)^(m-i))*y := by ring
  rw [he]
  simp only [map_add]
  ring
/-- Splitting an even-degree trace into its two conjugate halves. -/
theorem trace_even_split (n : ℕ) (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (z : B) :
    algebraMap k B (Algebra.trace k B z) =
      ∑ j ∈ Finset.range n, (z+z^((Fintype.card k)^n))^((Fintype.card k)^j) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    finrank_eq_of_card (k:=k) (2*n) hcard]
  simp only [Nat.card_eq_fintype_card]
  rw [two_mul,Finset.sum_range_add]
  simp only [scalar_frobenius_add (k:=k),Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.pow_add,pow_mul]

/-- The middle half-trace block has the same trace-pairing polar formula. -/
theorem halfTracePolynomial_polar (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (c x y : B) (hc : c^((Fintype.card k)^n)=c) :
    (halfTracePolynomial (k:=k) n c).eval (x+y) -
      (halfTracePolynomial (k:=k) n c).eval x -
      (halfTracePolynomial (k:=k) n c).eval y =
    algebraMap k B (Algebra.trace k B
      (y*(halfTracePolynomial (k:=k) n c).derivative.eval x)) := by
  rw [halfTracePolynomial_eval_sum,halfTracePolynomial_eval_sum,
    halfTracePolynomial_eval_sum,halfTracePolynomial_derivative _ hn]
  simp only [eval_mul,eval_C,eval_pow,eval_X]
  rw [trace_even_split n hcard]
  have hx : (x^((Fintype.card k)^n))^((Fintype.card k)^n)=x := by
    rw [← pow_mul,← Nat.pow_add,← two_mul,← hcard,FiniteField.pow_card]
  have he : y*(c*x^((Fintype.card k)^n))+
      (y*(c*x^((Fintype.card k)^n)))^((Fintype.card k)^n) =
      c*x^((Fintype.card k)^n)*y+c*x*y^((Fintype.card k)^n) := by
    rw [mul_pow,mul_pow,hc,hx]
    ring
  rw [he]
  have hexp : c*(x+y)^((Fintype.card k)^n+1) =
      c*x^((Fintype.card k)^n+1)+c*y^((Fintype.card k)^n+1)+
        (c*x^((Fintype.card k)^n)*y+c*x*y^((Fintype.card k)^n)) := by
    simp only [pow_succ,scalar_frobenius_add (k:=k)]
    ring
  simp only [hexp,scalar_frobenius_add (k:=k),Finset.sum_add_distrib]
  ring
/-- The concrete trace family has the field-trace pairing with its derivative as polar form. -/
theorem traceFamilyPolynomial_polar (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (a : TraceFamilyIndex n t → B) (c : B)
    (hc : c^((Fintype.card k)^n)=c) (x y : B) :
    (traceFamilyPolynomial (k:=k) n t a c).eval (x+y) -
      (traceFamilyPolynomial (k:=k) n t a c).eval x -
      (traceFamilyPolynomial (k:=k) n t a c).eval y =
    algebraMap k B (Algebra.trace k B
      (y*(traceFamilyPolynomial (k:=k) n t a c).derivative.eval x)) := by
  have hi (i : TraceFamilyIndex n t) : 0 < i.val.val ∧ i.val.val < 2*n := by
    have := i.property
    have := i.val.isLt
    omega
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun (i : TraceFamilyIndex n t) _ =>
      cyclicTracePolynomial_polar (2*n) i.val.val (hi i).1 (hi i).2 hcard (a i) x y)
  have hh := halfTracePolynomial_polar n (by omega) hcard c x y hc
  simp only [Finset.sum_sub_distrib,← map_sum,← Finset.mul_sum] at hs
  simp only [traceFamilyPolynomial,eval_add,eval_finsetSum,
    Finset.mul_sum,mul_add,map_add,map_sum]
  simp only [map_sum,Finset.mul_sum] at hs
  linear_combination hs + hh

/-- Nondegeneracy of the actual finite-field trace pairing detects zero. -/
theorem trace_pairing_eq_zero_iff (z : B) :
    (∀ y : B, algebraMap k B (Algebra.trace k B (y*z))=0) ↔ z=0 := by
  constructor
  · intro h
    apply (traceForm_nondegenerate k B).1 z
    intro y
    change Algebra.trace k B (z*y)=0
    apply (algebraMap k B).injective
    simpa [mul_comm] using h y
  · rintro rfl
    simp

/-- The polar radical of the actual polynomial is exactly its derivative zero set. -/
theorem traceFamily_polar_radical_iff (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hcard : Fintype.card B = (Fintype.card k)^(2*n))
    (a : TraceFamilyIndex n t → B) (c : B)
    (hc : c^((Fintype.card k)^n)=c) (x : B) :
    (∀ y : B, (traceFamilyPolynomial (k:=k) n t a c).eval (x+y) -
      (traceFamilyPolynomial (k:=k) n t a c).eval x -
      (traceFamilyPolynomial (k:=k) n t a c).eval y = 0) ↔
      (traceFamilyPolynomial (k:=k) n t a c).derivative.eval x=0 := by
  simp only [traceFamilyPolynomial_polar n t ht htn hcard a c hc x]
  exact trace_pairing_eq_zero_iff _
end BinaryFieldCounterexamples.QuadraticFormTrace
