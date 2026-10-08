/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceHyperplaneLocators
public import BinaryFieldCounterexamples.Polynomial.QuadraticFactorSupport
/-!
# Sparse factors and their actual domain root counts

The converted factors of minimum-rank trace polynomials inherit literal
Frobenius support divisibility. Their zeros are exactly the derivative zeros,
whose actual radical counts are known. Hyperplane descent divides that count
by q via the concrete map fibers. These facts keep the information needed
for sharp pairwise collision bounds after extending the field.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
set_option warn.classDefReducibility false
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- Exact factor support and radical-sized root count on the full field. -/
theorem translatedTracePolynomial_factor_properties
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c z : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n)=c)
    (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t)
    (A : B[X]) (lam : B) (hlam : lam ≠ 0)
    (hA : (translatedTracePolynomial (k := k) n t a c z).derivative = -C lam * A^(Fintype.card k)) :
    (∀ e ∈ A.support, (Fintype.card k)^(t-1) ∣ e) ∧
      (Finset.univ.filter (fun x : B => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t) := by
  constructor
  · rw [hq]
    apply quadratic_factor_support_dvd p r t ht A _ lam hlam (by simpa only [hq] using hA)
    intro e he
    simpa only [hq] using translatedTracePolynomial_derivative_support_dvd n t ht htn a c z hcard e he
  · have hsets : Finset.univ.filter (fun x : B => A.eval x=0) =
        Finset.univ.filter (fun x : B => (translatedTracePolynomial (k := k) n t a c z).derivative.eval x=0) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (scaled_power_eval_zero_iff (Fintype.card k) Fintype.card_pos A _ lam hlam hA x).symm
    rw [hsets]
    exact translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht htn a c z hcard hc hne hrank

/-- Exact factor support and radical-sized root count on the prescribed hyperplane. -/
theorem descendedTracePolynomial_factor_properties
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t<n)
    (a : TraceFamilyIndex n t → B) (c z v : B) (hv : v≠0)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n)=c)
    (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-Module.finrank k (traceFamilyQuadraticForm n t ht (by omega) a c hcard hc).radical=2*t)
    (D : Submodule k B) (hrange : LinearMap.range (hyperplaneMap (k := k) v)=D)
    (H A : B[X]) (lam : B) (hlam : lam≠0)
    (hd : H.derivative.comp (hyperplanePolynomial (k := k) v)=(translatedTracePolynomial (k := k) n t a c z).derivative)
    (hA : H.derivative = -C lam * A^(Fintype.card k)) :
    (∀ e ∈ A.support, (Fintype.card k)^(t-1) ∣ e) ∧
      ((Finset.univ.filter (fun x : B => x∈D)).filter (fun x => A.eval x=0)).card=(Fintype.card k)^(2*n-2*t-1) := by
  constructor
  · rw [hq]
    apply quadratic_factor_support_dvd p r t ht A H.derivative lam hlam (by simpa only [hq] using hA)
    intro e he
    rcases descendedTracePolynomial_derivative_support n t ht (by omega) a c z v hv hcard H hd e he with hz | ⟨i,hit,_,rfl⟩
    · simp [hz]
    · rw [←hq]
      exact pow_dvd_pow _ hit
  · have hcount : Nat.card {y : D // H.derivative.eval y.val=0} =
        ((Finset.univ.filter (fun x : B => x∈D)).filter (fun x => A.eval x=0)).card := by
      rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : B => x∈D) (fun x => H.derivative.eval x=0)),
        Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [scaled_power_eval_zero_iff (Fintype.card k) Fintype.card_pos A H.derivative lam hlam hA x]
    have hf := hyperplanePolynomial_zero_natCard v hv D hrange H.derivative
    rw [hd,hcount,Nat.card_eq_fintype_card,Fintype.card_subtype,
      translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht (by omega) a c z hcard hc hne hrank] at hf
    apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := k))
    rw [←hf, ←pow_succ']
    congr 1
    omega
end BinaryFieldCounterexamples.QuadraticFormTrace
