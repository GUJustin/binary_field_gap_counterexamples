/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QuadraticFactorExistence
/-!
# Frobenius support of converted quadratic factors

If the scaled q-th power of a factor has all support exponents divisible by
q^t, its own support exponents are divisible by q^(t-1). Literal coefficient
Frobenius proves the assertion, retaining the constant term when present.
This supplies the distinct-root bound needed for collision counting.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
variable {F : Type*} [Field F]
/-- Recover exact exponent divisibility from a scaled Frobenius-power identity. -/
theorem quadratic_factor_support_dvd (p r t : ℕ) [Fact p.Prime] [CharP F p]
    (ht : 1 ≤ t) (A J : F[X]) (lam : F) (hlam : lam ≠ 0)
    (hJ : J = -C lam * A^(p^r))
    (hs : ∀ e ∈ J.support, (p^r)^t ∣ e) :
    ∀ e ∈ A.support, (p^r)^(t-1) ∣ e := by
  intro e he
  have hp : 0 < p^r := pow_pos (Fact.out : p.Prime).pos _
  have hc : (A^(p^r)).coeff (e*(p^r)) ≠ 0 := by
    rw [← map_iterateFrobenius_expand p A r, coeff_map, coeff_expand_mul hp]
    rw [iterateFrobenius_def]
    exact pow_ne_zero _ (mem_support_iff.mp he)
  have hj : e*(p^r) ∈ J.support := by
    rw [mem_support_iff, hJ, neg_mul, coeff_neg, coeff_C_mul]
    exact neg_ne_zero.mpr (mul_ne_zero hlam hc)
  have hd := hs _ hj
  have heq : (p^r)^t = (p^r)^(t-1)*(p^r) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [heq] at hd
  exact Nat.dvd_of_mul_dvd_mul_right hp hd
/-- A nonzero scaled positive power has exactly the factor's evaluation zeros. -/
theorem scaled_power_eval_zero_iff (q : ℕ) (hq : 0 < q)
    (A J : F[X]) (lam : F) (hlam : lam ≠ 0) (hJ : J = -C lam * A^q) (x : F) :
    J.eval x = 0 ↔ A.eval x = 0 := by
  rw [hJ, eval_mul, eval_neg, eval_C, eval_pow, mul_eq_zero]
  simp only [neg_eq_zero, hlam, false_or, pow_eq_zero_iff hq.ne']
/-- Recover the scaled derivative factor from conversion and the differential identity. -/
theorem factor_derivative_of_conversion (q : ℕ) (hq : 1 ≤ q)
    (G A P L J : F[X]) (lam : F) (hlam : lam ≠ 0) (hL : L ≠ 0)
    (hG : G=A*P) (hconv : A^(q-1)*(P^q-L)=P)
    (hdiff : G^q-G = -C (lam⁻¹)*L*J) : J = -C lam * A^q := by
  have hp : A*(A^(q-1)*(P^q-L))=A*P := congrArg (fun S : F[X] => A*S) hconv
  have hap : A*A^(q-1)=A^q := by rw [←pow_succ']; congr 1; omega
  rw [←mul_assoc, hap] at hp
  have hpow : G^q-G=L*A^q := by rw [hG,mul_pow,←hp]; ring
  rw [hpow] at hdiff
  have hh : A^q = -C (lam⁻¹)*J := by
    apply mul_left_cancel₀ hL
    calc
      L*A^q = -C (lam⁻¹)*L*J := hdiff
      _ = L*(-C (lam⁻¹)*J) := by ring
  rw [hh]
  simp [←mul_assoc, ←C_mul, hlam]
end BinaryFieldCounterexamples
