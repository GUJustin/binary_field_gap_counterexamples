/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Polynomial.PrimePowerSupport
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Tactic.LinearCombination

/-!
# Concrete reduced quadratic trace polynomials

The cyclic blocks represent actual field traces and keep their literal
reduced exponents. The middle half-trace block uses an explicit Frobenius-fixed
coefficient, so no intermediate-field population is assumed. Their finite sum
is the manuscript's concrete trace family, with fixed values, exact derivative
indices, and the prescribed degree budget. Counting its elliptic rank stratum
is a separate mathematical task.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]

/-- The reduced cyclic representative of one ambient quadratic trace term. -/
noncomputable def cyclicTracePolynomial (m i : ℕ) (a : B) : B[X] :=
  ∑ j∈Finset.range m, C (a^((Fintype.card k)^j))*
    X^((Fintype.card k)^j+(Fintype.card k)^((i+j)%m))
/-- Frobenius exponents reduce cyclically modulo the actual extension dimension. -/
theorem pow_card_index_mod (m : ℕ) (hcard : Fintype.card B=(Fintype.card k)^m)
    (e : ℕ) (x : B) : x^((Fintype.card k)^e)=x^((Fintype.card k)^(e%m)) := by
  have hfixed := FiniteField.pow_card_pow (K:=B) (e/m) x
  have hindex : m*(e/m)+e%m=e := by
    simpa only [Nat.add_comm] using Nat.mod_add_div e m
  calc
    x^((Fintype.card k)^e)=x^((Fintype.card k)^(m*(e/m))*(Fintype.card k)^(e%m)) := by
      rw [←pow_add,hindex]
    _=(x^((Fintype.card k)^(m*(e/m))))^((Fintype.card k)^(e%m)) := by rw [pow_mul]
    _=x^((Fintype.card k)^(e%m)) := by rw [pow_mul,←hcard,hfixed]
/-- Evaluation of the literal reduced trace block is the sum of conjugates
of the intended quadratic monomial. -/
theorem cyclicTracePolynomial_eval_sum (m i : ℕ) (a x : B)
    (hcard : Fintype.card B=(Fintype.card k)^m) :
    (cyclicTracePolynomial (k:=k) m i a).eval x=
      ∑ j∈Finset.range m, (a*x^((Fintype.card k)^i+1))^((Fintype.card k)^j) := by
  simp only [cyclicTracePolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow,pow_add,pow_succ,mul_pow,←pow_mul,←pow_add (Fintype.card k) i j]
  rw [pow_card_index_mod m hcard (i+j) x]
  ring
/-- The cardinality hypothesis identifies the actual scalar extension dimension. -/
theorem finrank_eq_of_card (m : ℕ) (hcard : Fintype.card B=(Fintype.card k)^m) :
    Module.finrank k B=m := by
  have hc := Module.natCard_eq_pow_finrank (K:=k) (V:=B)
  simp only [Nat.card_eq_fintype_card] at hc
  rw [hcard] at hc
  exact (Nat.pow_right_injective Fintype.one_lt_card hc).symm
/-- The reduced cyclic polynomial represents the actual field trace. -/
theorem cyclicTracePolynomial_eval_trace (m i : ℕ) (a x : B)
    (hcard : Fintype.card B=(Fintype.card k)^m) :
    (cyclicTracePolynomial (k:=k) m i a).eval x=
      algebraMap k B (Algebra.trace k B (a*x^((Fintype.card k)^i+1))) := by
  rw [cyclicTracePolynomial_eval_sum m i a x hcard,
    FiniteField.algebraMap_trace_eq_sum_pow,finrank_eq_of_card m hcard,Nat.card_eq_fintype_card]
/-- Every value of the actual cyclic trace polynomial is fixed by scalar-field Frobenius. -/
theorem cyclicTracePolynomial_eval_fixed (m i : ℕ) (a x : B)
    (hcard : Fintype.card B=(Fintype.card k)^m) :
    ((cyclicTracePolynomial (k:=k) m i a).eval x)^(Fintype.card k)=
      (cyclicTracePolynomial (k:=k) m i a).eval x := by
  rw [cyclicTracePolynomial_eval_trace m i a x hcard,←map_pow,FiniteField.pow_card]
/-- The unique nonzero cyclic index which wraps to zero. -/
theorem cyclic_index_zero_iff (m i j : ℕ) (hi : 0  <  i) (him : i  <  m) (hj : j  <  m) :
    (i+j)%m=0 ↔ j=m-i := by
  by_cases h : i+j  <  m
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (show m ≤ i+j by omega),Nat.mod_eq_of_lt (show i+j-m < m by omega)]
    omega
/-- A cyclic quadratic trace block has exactly its two stated derivative indices. -/
theorem cyclicTracePolynomial_derivative (m i : ℕ) (hi : 0  <  i) (him : i  <  m) (a : B) :
    (cyclicTracePolynomial (k:=k) m i a).derivative=
      C a*X^((Fintype.card k)^i)+
      C (a^((Fintype.card k)^(m-i)))*X^((Fintype.card k)^(m-i)) := by
  have hq : ((Fintype.card k:ℕ):B)=0 := by
    rw [←map_natCast (algebraMap k B),FiniteField.cast_card_eq_zero,map_zero]
  have hmi : 0 < m-i ∧ m-i  <  m := by omega
  have hterm (j : ℕ) (hj : j∈Finset.range m) :
      (C (a^((Fintype.card k)^j))*X^((Fintype.card k)^j+(Fintype.card k)^((i+j)%m))).derivative=
      (if j=0 then C a*X^((Fintype.card k)^i) else 0)+
      (if j=m-i then C (a^((Fintype.card k)^(m-i)))*X^((Fintype.card k)^(m-i)) else 0) := by
    rw [derivative_C_mul_X_pow]
    by_cases hj0 : j=0
    · subst j
      simp [Nat.mod_eq_of_lt him,Nat.cast_pow,hq,hi.ne',Ne.symm hmi.1.ne']
    · by_cases hji : j=m-i
      · subst j
        have hr : (i+(m-i))%m=0 := (cyclic_index_zero_iff m i (m-i) hi him hmi.2).mpr rfl
        simp [hr,hj0,Nat.cast_pow,hq]
      · have hr : (i+j)%m≠0 := by
          intro hz
          exact hji ((cyclic_index_zero_iff m i j hi him (Finset.mem_range.mp hj)).mp hz)
        simp [hj0,hji,Nat.cast_pow,hq,hr]
  unfold cyclicTracePolynomial
  rw [derivative_sum]
  simp_rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq',hmi.2,show 0 < m by omega]
/-- Cyclic index separation bounds every reduced monomial by the same
literal high-degree budget. -/
theorem cyclicTracePolynomial_natDegree_le (m i t : ℕ) (hi : t  ≤  i) (him : i  ≤  m-t)
    (ht : 1 ≤ t) (a : B) :
    (cyclicTracePolynomial (k:=k) m i a).natDegree ≤
      (Fintype.card k)^(m-1)+(Fintype.card k)^(m-t-1) := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_X_pow]
  have hjm : j  <  m := Finset.mem_range.mp hj
  have hq : 1 ≤ Fintype.card k := Fintype.card_pos
  by_cases h : i+j  <  m
  · rw [Nat.mod_eq_of_lt h]
    have h1 : (Fintype.card k)^j ≤ (Fintype.card k)^(m-t-1) := Nat.pow_le_pow_right hq (by omega)
    have h2 : (Fintype.card k)^(i+j) ≤ (Fintype.card k)^(m-1) := Nat.pow_le_pow_right hq (by omega)
    omega
  · rw [Nat.mod_eq_sub_mod (show m ≤ i+j by omega),Nat.mod_eq_of_lt (show i+j-m < m by omega)]
    exact Nat.add_le_add (Nat.pow_le_pow_right hq (by omega))
      (Nat.pow_le_pow_right hq (by omega))
/-- The finite trace sum satisfies its literal Frobenius telescoping identity. -/
theorem trace_sum_frobenius_sub (n : ℕ) (z : B) :
    (∑ j∈Finset.range n, z^((Fintype.card k)^j))^(Fintype.card k)-
      (∑ j∈Finset.range n, z^((Fintype.card k)^j))=z^((Fintype.card k)^n)-z := by
  have hp : (∑ j∈Finset.range n, z^((Fintype.card k)^j))^(Fintype.card k)=
      ∑ j∈Finset.range n, z^((Fintype.card k)^(j+1)) := by
    have he := map_sum (FiniteField.frobeniusAlgHom k B)
      (fun j => z^((Fintype.card k)^j)) (Finset.range n)
    change (∑ j∈Finset.range n, z^((Fintype.card k)^j))^(Fintype.card k)=
      ∑ j∈Finset.range n, (z^((Fintype.card k)^j))^(Fintype.card k) at he
    simpa only [pow_succ,pow_mul] using he
  rw [hp]
  have he := Finset.sum_range_succ' (fun j => z^((Fintype.card k)^j)) n
  rw [Finset.sum_range_succ] at he
  simp only [pow_zero,pow_one] at he
  linear_combination -he
/-- The literal half-trace block for the norm monomial in even dimension. -/
noncomputable def halfTracePolynomial (n : ℕ) (a : B) : B[X] :=
  ∑ j∈Finset.range n, C (a^((Fintype.card k)^j))*
    X^((Fintype.card k)^j+(Fintype.card k)^(n+j))
/-- The half-trace polynomial evaluates to the partial trace of the norm monomial. -/
theorem halfTracePolynomial_eval_sum (n : ℕ) (a x : B) :
    (halfTracePolynomial (k:=k) n a).eval x=
      ∑ j∈Finset.range n, (a*x^((Fintype.card k)^n+1))^((Fintype.card k)^j) := by
  simp only [halfTracePolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow,pow_add,pow_succ,mul_pow,←pow_mul,←pow_add (Fintype.card k) n j]
  ring
/-- The explicit half-field coefficient condition makes every norm-trace
value fixed by scalar-field Frobenius; no intermediate field is assumed. -/
theorem halfTracePolynomial_eval_fixed (n : ℕ) (a x : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (ha : a^((Fintype.card k)^n)=a) :
    ((halfTracePolynomial (k:=k) n a).eval x)^(Fintype.card k)=
      (halfTracePolynomial (k:=k) n a).eval x := by
  have hx : (x^((Fintype.card k)^n))^((Fintype.card k)^n)=x := by
    rw [←pow_mul,←pow_add,show n+n=2*n by omega,←hcard]
    exact FiniteField.pow_card x
  have hz : (a*x^((Fintype.card k)^n+1))^((Fintype.card k)^n)=
      a*x^((Fintype.card k)^n+1) := by
    rw [mul_pow,ha,pow_succ,mul_pow,hx]
    ring
  rw [halfTracePolynomial_eval_sum]
  apply sub_eq_zero.mp
  rw [trace_sum_frobenius_sub,hz,sub_self]
/-- The half-trace block has exactly its middle derivative index. -/
theorem halfTracePolynomial_derivative (n : ℕ) (hn : 0 < n) (a : B) :
    (halfTracePolynomial (k:=k) n a).derivative=C a*X^((Fintype.card k)^n) := by
  have hq : ((Fintype.card k:ℕ):B)=0 := by
    rw [←map_natCast (algebraMap k B),FiniteField.cast_card_eq_zero,map_zero]
  have hterm (j : ℕ) (hj : j∈Finset.range n) :
      (C (a^((Fintype.card k)^j))*X^((Fintype.card k)^j+(Fintype.card k)^(n+j))).derivative=
      if j=0 then C a*X^((Fintype.card k)^n) else 0 := by
    rw [derivative_C_mul_X_pow]
    by_cases hj0 : j=0
    · subst j
      simp [Nat.cast_pow,hq,hn.ne']
    · simp [hj0,Nat.cast_pow,hq]
  unfold halfTracePolynomial
  rw [derivative_sum,Finset.sum_congr rfl hterm]
  simp [Finset.sum_ite_eq',hn]
/-- The half-trace block obeys the precise reduced degree budget. -/
theorem halfTracePolynomial_natDegree_le (n : ℕ) (a : B) :
    (halfTracePolynomial (k:=k) n a).natDegree ≤
      (Fintype.card k)^(2*n-1)+(Fintype.card k)^(n-1) := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_X_pow]
  have hjn : j < n := Finset.mem_range.mp hj
  have hq : 1 ≤ Fintype.card k := Fintype.card_pos
  have h1 : (Fintype.card k)^j ≤ (Fintype.card k)^(n-1) := Nat.pow_le_pow_right hq (by omega)
  have h2 : (Fintype.card k)^(n+j) ≤ (Fintype.card k)^(2*n-1) := Nat.pow_le_pow_right hq (by omega)
  omega
/-- The finite off-middle coefficient positions of the manuscript family. -/
def TraceFamilyIndex (n t : ℕ) := {i : Fin n // t ≤ (i:ℕ)}
/-- The coefficient positions form the literal finite index set. -/
noncomputable def traceFamilyIndexFintype (n t : ℕ) : Fintype (TraceFamilyIndex n t) :=
  inferInstanceAs (Fintype {i : Fin n // t ≤ (i:ℕ)})
attribute [local instance] traceFamilyIndexFintype
/-- The concrete quadratic trace family, with the half-field coefficient
condition imposed explicitly by theorems consuming its middle coefficient. -/
noncomputable def traceFamilyPolynomial (n t : ℕ) (a : TraceFamilyIndex n t → B) (c : B) : B[X] :=
  (∑ i : TraceFamilyIndex n t, cyclicTracePolynomial (k:=k) (2*n) i.val.val (a i))+
    halfTracePolynomial (k:=k) n c
/-- Every value of the concrete family lies in the scalar-field fixed set. -/
theorem traceFamilyPolynomial_eval_fixed (n t : ℕ) (a : TraceFamilyIndex n t → B) (c x : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (hc : c^((Fintype.card k)^n)=c) :
    ((traceFamilyPolynomial (k:=k) n t a c).eval x)^(Fintype.card k)=
      (traceFamilyPolynomial (k:=k) n t a c).eval x := by
  simp only [traceFamilyPolynomial,eval_add,eval_finsetSum]
  change (FiniteField.frobeniusAlgHom k B) (_+_)=_
  rw [map_add,map_sum]
  simp only [FiniteField.frobeniusAlgHom_apply]
  rw [halfTracePolynomial_eval_fixed n c x hcard hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact cyclicTracePolynomial_eval_fixed (2*n) i.val.val (a i) x hcard
/-- The concrete family has the prescribed literal derivative coefficient formula. -/
theorem traceFamilyPolynomial_derivative (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) :
    (traceFamilyPolynomial (k:=k) n t a c).derivative=
      (∑ i : TraceFamilyIndex n t,
        (C (a i)*X^((Fintype.card k)^i.val.val)+
          C ((a i)^((Fintype.card k)^(2*n-i.val.val)))*X^((Fintype.card k)^(2*n-i.val.val))))+
      C c*X^((Fintype.card k)^n) := by
  unfold traceFamilyPolynomial
  rw [derivative_add,derivative_sum,halfTracePolynomial_derivative n (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hil := i.property
  have hiu := i.val.isLt
  exact cyclicTracePolynomial_derivative (2*n) i.val.val (by omega) (by omega) (a i)
/-- The actual reduced family has the manuscript's degree bound before translation. -/
theorem traceFamilyPolynomial_natDegree_le (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (a : TraceFamilyIndex n t → B) (c : B) :
    (traceFamilyPolynomial (k:=k) n t a c).natDegree ≤
      (Fintype.card k)^(2*n-1)+(Fintype.card k)^(2*n-t-1) := by
  unfold traceFamilyPolynomial
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    have hil := i.property
    have hiu := i.val.isLt
    exact cyclicTracePolynomial_natDegree_le (2*n) i.val.val t hil (by omega) ht (a i)
  · apply (halfTracePolynomial_natDegree_le n c).trans
    apply Nat.add_le_add_left
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
end BinaryFieldCounterexamples.QuadraticFormTrace
