/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceFactors
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.DegenerateZeroCount
/-!
# Exact degrees and zero counts of translated trace polynomials

The elliptic zero count is unchanged by translation. Together with the exact
radical multiplicities, it saturates the polynomial degree bound. Splitting
and uniform multiplicity similarly determine the derivative's exact degree.
-/
@[expose] public section
set_option warn.classDefReducibility false
namespace BinaryFieldCounterexamples

/-- The elliptic zero count and extra radical multiplicities sum to the exact degree bound. -/
theorem elliptic_zero_plus_radical_weight (q m t : ℕ) (hq : 2≤q) (ht : 1≤t) (hm : 2*t≤m) :
    q^(m-1)-(q-1)*q^(m-t-1)+q^t*q^(m-2*t)=q^(m-1)+q^(m-t-1) := by
  have he1 : q^t*q^(m-t-1)=q^(m-1) := by rw [←pow_add]; congr 1; omega
  have he2 : q^t*q^(m-2*t)=q*q^(m-t-1) := by
    rw [←pow_add,←pow_succ']; congr 1; omega
  have hle : (q-1)*q^(m-t-1)≤q^(m-1) := by
    rw [←he1]
    apply Nat.mul_le_mul_right
    exact (Nat.sub_le q 1).trans (Nat.le_self_pow (by omega) _)
  have hh := Nat.sub_add_cancel hle
  rw [he2]
  have hq' : q-1+1=q := by omega
  have hmul := congrArg (fun z : ℕ => z*q^(m-t-1)) hq'
  simp only [Nat.add_mul,one_mul] at hmul
  omega
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples.QuadraticFormTrace
open Polynomial
attribute [local instance] Classical.decEq Classical.propDecidable traceFamilyIndexFintype
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
theorem translatedTracePolynomial_zero_card_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    (Finset.univ.filter (fun x : B => (translatedTracePolynomial (k:=k) n t a c v).eval x=0)).card=
      (Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) := by
  rw [←traceFamilyQuadraticForm_zero_card_of_exact_rank p r hr hq n t ht htn a c
    hcard hc hne hrank]
  apply Finset.card_bij (fun x _ => x-v)
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    rw [translatedTracePolynomial_eval,←algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc] at hx
    exact (algebraMap k B).injective (hx.trans (map_zero _).symm)
  · intro x hx y hy he
    exact sub_left_injective he
  · intro y hy
    refine ⟨y+v,?_,by simp⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy ⊢
    rw [translatedTracePolynomial_eval,add_sub_cancel_right,
      ←algebraMap_traceFamilyQuadraticForm n t ht htn a c hcard hc,hy,map_zero]

theorem translatedTracePolynomial_natDegree_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hr : 1≤r) (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    (translatedTracePolynomial (k:=k) n t a c v).natDegree=
      (Fintype.card k)^(2*n-1)+(Fintype.card k)^(2*n-t-1) := by
  let G := translatedTracePolynomial (k:=k) n t a c v
  let S := Finset.univ.filter (fun x : B => G.eval x=0)
  let R := Finset.univ.filter (fun x : B => G.derivative.eval x=0)
  have hdiv : G.derivative∣G := translatedTracePolynomial_derivative_dvd_of_exact_rank
    p r hr hq n t ht htn a c v hcard hc hne hrank
  have hG : G≠0 := by
    intro hz
    have hh := translatedTracePolynomial_derivative_ne_zero (k:=k) n t ht htn a c v hne
    apply hh
    change G.derivative=0
    rw [hz,derivative_zero]
  have hRS : R⊆S := by
    intro x hx
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (Finset.mem_filter.mp hx).2⟩
  have hl := weighted_root_card_le_natDegree G hG S R hRS ((Fintype.card k)^t)
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx => (translatedTracePolynomial_multiplicity_of_exact_rank p r hr hq n t ht htn
      a c v hcard hc hne hrank x (Finset.mem_filter.mp hx).2).ge)
  have hS : S.card=(Fintype.card k)^(2*n-1)-(Fintype.card k-1)*(Fintype.card k)^(2*n-t-1) :=
    translatedTracePolynomial_zero_card_of_exact_rank p r hr hq n t ht htn a c v hcard hc hne hrank
  have hR : R.card=(Fintype.card k)^(2*n-2*t) :=
    translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht htn a c v hcard hc hne hrank
  rw [hS,hR,elliptic_zero_plus_radical_weight _ _ _ Fintype.one_lt_card ht (by omega)] at hl
  exact le_antisymm (translatedTracePolynomial_natDegree_le n t ht htn a c v) hl

theorem translatedTracePolynomial_derivative_natDegree_of_exact_rank
    (p r : ℕ) [Fact p.Prime] [CharP B p] (hq : Fintype.card k=p^r)
    (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (a : TraceFamilyIndex n t → B) (c v : B)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n))
    (hc : c^((Fintype.card k)^n)=c) (hne : a≠0 ∨ c≠0)
    (hrank : Module.finrank k B-
      Module.finrank k (traceFamilyQuadraticForm n t ht htn a c hcard hc).radical=2*t) :
    (translatedTracePolynomial (k:=k) n t a c v).derivative.natDegree=
      (Fintype.card k)^(2*n-t) := by
  let J := (translatedTracePolynomial (k:=k) n t a c v).derivative
  have hJ : J≠0 := translatedTracePolynomial_derivative_ne_zero n t ht htn a c v hne
  have hs : J.Splits := translatedTracePolynomial_derivative_splits_of_exact_rank
    p r hq n t ht htn a c v hcard hc hne hrank
  have hroots : J.roots.toFinset=Finset.univ.filter (fun x : B => J.eval x=0) := by
    ext x
    simp [mem_roots hJ,IsRoot.def]
  calc
    J.natDegree=∑ x∈J.roots.toFinset,rootMultiplicity x J := by
      rw [hs.natDegree_eq_card_roots]
      simp only [←count_roots]
      exact (Multiset.toFinset_sum_count_eq _).symm
    _=∑ _x∈J.roots.toFinset,(Fintype.card k)^t := by
      apply Finset.sum_congr rfl
      intro x hx
      exact translatedTracePolynomial_derivative_multiplicity_of_exact_rank p r hq n t ht htn
        a c v hcard hc hne hrank x ((mem_roots hJ).mp (Multiset.mem_toFinset.mp hx))
    _=(Fintype.card k)^(2*n-t) := by
      rw [hroots,Finset.sum_const,Finset.card_filter]
      have hcR := translatedTracePolynomial_derivative_root_card_of_exact_rank p r hq n t ht htn
        a c v hcard hc hne hrank
      simp only [Finset.card_filter] at hcR
      rw [hcR]
      simp only [nsmul_eq_mul,Nat.cast_id,←pow_add]
      congr 1
      omega
end BinaryFieldCounterexamples.QuadraticFormTrace
