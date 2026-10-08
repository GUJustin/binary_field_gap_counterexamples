/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.QuadraticLocatorConversion

/-!
# Roots and multiplicities in quadratic locator conversion

Factoring the differential identity as `G*(G^(b-1)-1)` determines each root
multiplicity exactly. The actual converted polynomial has the same distinct
roots as `G`; when radical-factor roots lie in the domain, no exterior roots
occur. Domain and radical root hypotheses remain explicit.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
attribute [local instance] Classical.decEq
variable {K : Type*} [Field K]

/-- Multiplicity of an actual nonzero polynomial power scales by its exponent. -/
theorem rootMultiplicity_power (A : K[X]) (hA : A≠0) (x : K) (b : ℕ) :
    rootMultiplicity x (A^b)=b*rootMultiplicity x A := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hA) hA),ih]
    ring
/-- At every root of `G`, the differential factorization fixes its exact
multiplicity in terms of the domain locator and the Frobenius factor. -/
theorem rootMultiplicity_of_differential (G A L : K[X]) (b : ℕ)
    (hb : 2≤b) (hA : A≠0) (hL : L≠0)
    (hdifferential : G^b-G=L*A^b) (x : K) (hx : G.IsRoot x) :
    rootMultiplicity x G=rootMultiplicity x L+b*rootMultiplicity x A := by
  have hpow : G*G^(b-1)=G^b := by
    rw [←pow_succ']
    congr 1
    omega
  have hfactor : G*(G^(b-1)-1)=L*A^b := by
    rw [mul_sub,hpow,mul_one]
    exact hdifferential
  have hsecond : ¬(G^(b-1)-1).IsRoot x := by
    simp only [IsRoot,eval_sub,eval_pow,eval_one,hx.eq_zero,
      zero_pow (show b-1≠0 by omega),zero_sub,neg_ne_zero]
    exact one_ne_zero
  have hm := congrArg (rootMultiplicity x) hfactor
  rw [rootMultiplicity_mul (hfactor.symm ▸ mul_ne_zero hL (pow_ne_zero _ hA)),
    rootMultiplicity_eq_zero hsecond,add_zero,
    rootMultiplicity_mul (mul_ne_zero hL (pow_ne_zero _ hA)),
    rootMultiplicity_power A hA] at hm
  exact hm
/-- Simple domain roots make the radical-root multiplicity exactly one more
than the Frobenius-scaled factor multiplicity. -/
theorem rootMultiplicity_of_simple_domain (G A L : K[X]) (b : ℕ)
    (hb : 2≤b) (hA : A≠0) (hL : L≠0)
    (hdifferential : G^b-G=L*A^b) (x : K) (hx : G.IsRoot x)
    (hLx : rootMultiplicity x L=1) :
    rootMultiplicity x G=1+b*rootMultiplicity x A := by
  rw [rootMultiplicity_of_differential G A L b hb hA hL hdifferential x hx,hLx]
/-- The conversion identity preserves every distinct root of the original
function polynomial, including the radical roots. -/
theorem converted_isRoot_iff (G A P L : K[X]) (b : ℕ) (hb : 2≤b)
    (hfactor : G=A*P) (hconversion : A^(b-1)*(P^b-L)=P) (x : K) :
    P.IsRoot x ↔ G.IsRoot x := by
  simp only [hfactor,IsRoot,eval_mul]
  constructor
  · intro hx
    rw [hx,mul_zero]
  · intro hx
    rcases mul_eq_zero.mp hx with ha | hp
    · have he := congrArg (fun R : K[X] => R.eval x) hconversion
      simp only [eval_mul,eval_pow,eval_sub,ha,zero_pow (show b-1≠0 by omega),zero_mul] at he
      exact he.symm
    · exact hp
/-- When every radical-factor root lies in the domain locator, the
differential identity excludes all exterior roots of the function polynomial. -/
theorem isRoot_domain_of_isRoot_function (G A L : K[X]) (b : ℕ) (hb : 1≤b)
    (hdifferential : G^b-G=L*A^b)
    (hAroots : ∀ x : K, A.IsRoot x → L.IsRoot x)
    (x : K) (hx : G.IsRoot x) : L.IsRoot x := by
  have he := congrArg (fun R : K[X] => R.eval x) hdifferential
  simp only [eval_sub,eval_pow,eval_mul,hx.eq_zero] at he
  rw [zero_pow (show b≠0 by omega),sub_zero] at he
  rcases mul_eq_zero.mp he.symm with hL | hA
  · exact hL
  · exact hAroots x (eq_zero_of_pow_eq_zero hA)
/-- The conversion preserves the literal finite set of distinct roots. -/
theorem converted_roots_toFinset_eq (G A P L : K[X]) (b : ℕ) (hb : 2≤b)
    (hG : G≠0) (hfactor : G=A*P) (hconversion : A^(b-1)*(P^b-L)=P) :
    P.roots.toFinset=G.roots.toFinset := by
  classical
  have hP : P≠0 := by intro hz; rw [hfactor,hz,mul_zero] at hG; exact hG rfl
  ext x
  simp only [Multiset.mem_toFinset,mem_roots hP,mem_roots hG]
  exact converted_isRoot_iff G A P L b hb hfactor hconversion x
/-- The converted locator is nonzero at every exterior pole once all
radical-factor roots lie in the actual domain locator. -/
theorem converted_eval_ne_zero_of_exterior (G A P L : K[X]) (b : ℕ) (hb : 2≤b)
    (hfactor : G=A*P) (hconversion : A^(b-1)*(P^b-L)=P)
    (hdifferential : G^b-G=L*A^b)
    (hAroots : ∀ x : K, A.IsRoot x → L.IsRoot x)
    (x : K) (houtside : L.eval x≠0) : P.eval x≠0 := by
  intro hx
  have hG := (converted_isRoot_iff G A P L b hb hfactor hconversion x).mp hx
  exact houtside (isRoot_domain_of_isRoot_function G A L b (by omega) hdifferential hAroots x hG)
end BinaryFieldCounterexamples.QuadraticLocatorConversion
