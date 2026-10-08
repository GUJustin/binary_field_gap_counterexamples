/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# General-characteristic quadratic locator conversion

The literal differential and factorization identities imply the polynomial
conversion identity. It recovers the factor up to at most `b-1` choices and
controls nonzero evaluation collisions. A supplied Frobenius common head gives
an actual strict-degree correction. These algebraic prerequisites do not assume
or construct the quadratic-form population or its root multiplicities.

The conversion follows `sections/constructions/fullfield-elliptic.tex`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticLocatorConversion
open Polynomial
variable {K : Type*} [Field K]

/-- The differential identity and actual factorization give the locator
conversion identity after cancelling the nonzero factor. -/
theorem conversion_identity (G A P L : K[X]) (lam : K) (b : ℕ)
    (hb : 2≤b) (hlam : lam≠0) (hA : A≠0) (hfactor : G=A*P)
    (hderiv : G.derivative= -C lam*A^b)
    (hdifferential : G^b-G= -C (lam⁻¹)*L*G.derivative) :
    A^(b-1)*(P^b-L)=P := by
  have hd : G^b-G=L*A^b := by
    rw [hdifferential,hderiv]
    calc
      -C (lam⁻¹)*L*(-C lam*A^b)=C (lam⁻¹*lam)*(L*A^b) := by
        rw [map_mul]
        ring
      _=L*A^b := by simp [hlam]
  have hp : A*A^(b-1)=A^b := by
    rw [←pow_succ']
    congr 1
    omega
  apply mul_left_cancel₀ hA
  rw [←mul_assoc,hp]
  rw [hfactor,mul_pow] at hd
  calc
    A^b*(P^b-L)=(A^b*P^b-A*P)-L*A^b+A*P := by ring
    _=A*P := by rw [hd]; ring
/-- Equal nonzero leading coefficients in the literal factorization make
the converted polynomial monic. -/
theorem monic_of_factor_leadingCoeff (G A P : K[X]) (hA : A≠0)
    (hfactor : G=A*P) (hlead : G.leadingCoeff=A.leadingCoeff) : P.Monic := by
  change P.leadingCoeff=1
  apply mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hA)
  rw [mul_one,←leadingCoeff_mul,←hfactor]
  exact hlead
/-- The converted locator recovers the `(b-1)`st power of its factor. -/
theorem factor_power_eq (A B P L : K[X]) (b : ℕ) (hP : P≠0)
    (hA : A^(b-1)*(P^b-L)=P) (hB : B^(b-1)*(P^b-L)=P) :
    A^(b-1)=B^(b-1) := by
  have hd : P^b-L≠0 := by
    intro hz
    rw [hz,mul_zero] at hA
    exact hP hA.symm
  exact mul_right_cancel₀ hd (hA.trans hB.symm)
/-- A nonzero converted polynomial has at most `b-1` distinct factor
representatives; this counts actual polynomials, without assuming split roots. -/
theorem factor_fiber_card_le (P L : K[X]) (b : ℕ) (hb : 2≤b) (hP : P≠0)
    (S : Finset K[X]) (hS : ∀ A∈S, A^(b-1)*(P^b-L)=P) : S.card≤b-1 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨A,hA⟩ := hs
    let Q : (K[X])[X] := X^(b-1)-C (A^(b-1))
    have hQ : Q≠0 := by
      have hd : Q.natDegree=b-1 := natDegree_X_pow_sub_C
      intro hz
      rw [hz,natDegree_zero] at hd
      omega
    have hsub : S⊆Q.roots.toFinset := by
      intro B hB
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hQ).mpr
      change Q.eval B=0
      simp only [Q,eval_sub,eval_pow,eval_X,eval_C]
      exact sub_eq_zero.mpr (factor_power_eq B A P L b hP (hS B hB) (hS A hA))
    calc
      S.card≤Q.roots.toFinset.card := Finset.card_le_card hsub
      _≤Q.roots.card := Multiset.toFinset_card_le _
      _≤Q.natDegree := card_roots' Q
      _=b-1 := natDegree_X_pow_sub_C
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]
/-- A collision at a nonzero locator value forces the factor values to
have the same `(b-1)`st power. -/
theorem factor_eval_power_eq_of_collision (A B P Q L : K[X]) (b : ℕ) (x : K)
    (hA : A^(b-1)*(P^b-L)=P) (hB : B^(b-1)*(Q^b-L)=Q)
    (hcollision : P.eval x=Q.eval x) (hne : P.eval x≠0) :
    (A.eval x)^(b-1)=(B.eval x)^(b-1) := by
  have ha := congrArg (fun R : K[X] => R.eval x) hA
  have hb := congrArg (fun R : K[X] => R.eval x) hB
  simp only [eval_mul,eval_pow,eval_sub] at ha hb
  rw [←hcollision] at hb
  have hd : (P.eval x)^b-L.eval x≠0 := by
    intro hz
    rw [hz,mul_zero] at ha
    exact hne ha.symm
  exact mul_right_cancel₀ hd (ha.trans hb.symm)
/-- At a nonzero collision, the two factor values differ by an actual
`(b-1)`st root of unity. -/
theorem factor_eval_scalar_of_collision (A B P Q L : K[X]) (b : ℕ) (hb : 2≤b) (x : K)
    (hA : A^(b-1)*(P^b-L)=P) (hB : B^(b-1)*(Q^b-L)=Q)
    (hcollision : P.eval x=Q.eval x) (hne : P.eval x≠0) :
    ∃ zeta : K, zeta^(b-1)=1 ∧ A.eval x=zeta*B.eval x := by
  have he := factor_eval_power_eq_of_collision A B P Q L b x hA hB hcollision hne
  have hB0 : B.eval x≠0 := by
    intro hz
    have hh := congrArg (fun R : K[X] => R.eval x) hB
    simp only [eval_mul,eval_pow,eval_sub,hz,zero_pow (show b-1≠0 by omega),zero_mul] at hh
    exact hne (hcollision.trans hh.symm)
  refine ⟨A.eval x/B.eval x,?_,?_⟩
  · rw [div_pow,he,div_self (pow_ne_zero _ hB0)]
  · exact (div_mul_cancel₀ _ hB0).symm
/-- A literal Frobenius identity with a small remainder proves the strict
common-head degree bound in arbitrary prime-power characteristic. -/
theorem common_head_natDegree_lt (P R S : K[X]) (p r k : ℕ) [ExpChar K p]
    (hidentity : P^(p^r)-R^(p^r)=S) (hdegree : S.natDegree<p^r*k) :
    (P-R).natDegree<k := by
  have hp : (P-R)^(p^r)=S := by rw [sub_pow_expChar_pow]; exact hidentity
  have hd : p^r*(P-R).natDegree=S.natDegree := by rw [←natDegree_pow,hp]
  rw [←hd] at hdegree
  exact lt_of_mul_lt_mul_left hdegree (Nat.zero_le _)
/-- The concrete identity `P^b=L-lam*S` can be compared against any supplied
literal common head, keeping a strict coefficient-degree bound. -/
theorem common_head_of_conversion (P R S L Q : K[X]) (lam : K)
    (p r k : ℕ) [ExpChar K p]
    (hP : P^(p^r)=L-C lam*S) (hR : R^(p^r)=L-Q)
    (hdegree : (Q-C lam*S).natDegree<p^r*k) : (P-R).natDegree<k := by
  apply common_head_natDegree_lt P R (Q-C lam*S) p r k
  · rw [hP,hR]
    ring
  · exact hdegree
/-- The common-head conversion supplies an actual strict-degree correction
polynomial, as required by the code's strict degree convention. -/
theorem exists_strict_common_head_correction (P R S L Q : K[X]) (lam : K)
    (p r k : ℕ) [ExpChar K p]
    (hP : P^(p^r)=L-C lam*S) (hR : R^(p^r)=L-Q)
    (hdegree : (Q-C lam*S).natDegree<p^r*k) :
    ∃ U : K[X], P=R+U ∧ U.degree<k := by
  refine ⟨P-R,by ring,?_⟩
  have hd := common_head_of_conversion P R S L Q lam p r k hP hR hdegree
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
end BinaryFieldCounterexamples.QuadraticLocatorConversion
