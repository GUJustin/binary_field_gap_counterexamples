/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.TraceRadicalIncidence
public import BinaryFieldCounterexamples.Constructions.QuadraticForms.HyperbolicIncidenceRecurrence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
@[expose] public section
namespace BinaryFieldCounterexamples
/-- The exact Gaussian dimension ratio, including both boundary choices. -/
theorem gaussianPascal_dimension_ratio (q n t : ℕ) (hq : 1<q) (ht : t≤n) :
    gaussianPascal q n t*(q^(n-t)-1)=gaussianPascal q (n-1) t*(q^n-1) := by
  by_cases ht0 : t=0
  · subst t
    simp [gaussianPascal_zero]
  · have hn : 1≤n := by omega
    have hp : gaussianPascal q n t=gaussianPascal q (n-1) (t-1)+q^t*gaussianPascal q (n-1) t := by
      conv_lhs => rw [show n=(n-1)+1 by omega,show t=(t-1)+1 by omega]
      rw [gaussianPascal,Nat.sub_add_cancel (by omega : 1≤t)]
    have ha := QuadraticGeometry.gaussianPascal_adjacent q (n-1) (t-1) hq (by omega)
    rw [Nat.sub_add_cancel (by omega : 1≤t),show n-1-(t-1)=n-t by omega] at ha
    have hc := congrArg (fun z : ℕ => (z:ℚ)) hp
    push_cast at hc
    have hpow : (q:ℚ)^t*(q:ℚ)^(n-t)=(q:ℚ)^n := by rw [←pow_add]; congr 1; omega
    have hh : (gaussianPascal q n t:ℚ)*((q:ℚ)^(n-t)-1)=
        (gaussianPascal q (n-1) t:ℚ)*((q:ℚ)^n-1) := by
      rw [hc,←hpow]
      linear_combination -ha
    have hq1 : 1≤q := by omega
    have hp1 : 1≤q^(n-t) := Nat.one_le_pow _ _ hq1
    have hp2 : 1≤q^n := Nat.one_le_pow _ _ hq1
    exact_mod_cast hh
end BinaryFieldCounterexamples
namespace BinaryFieldCounterexamples.QuadraticFormTrace
attribute [local instance] Classical.decEq Classical.propDecidable
variable {k B : Type*} [Field k] [Fintype k] [Field B] [Fintype B] [Algebra k B]
/-- The literal trace rank layer whose quadratic radicals contain the prescribed hyperplane kernel vector. -/
noncomputable def traceHyperplaneRankFamily (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (v : B) : Finset (QuadraticForm k B) :=
  (traceRankFamily n t ht htn hcard (2*t)).filter (fun Q => v∈Q.radical)
/-- Every member of the hyperplane family is an actual trace-family form of the required rank and radical incidence. -/
theorem mem_traceHyperplaneRankFamily (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (v : B) (Q : QuadraticForm k B) :
    Q∈traceHyperplaneRankFamily n t ht htn hcard v ↔
      Q∈traceQuadraticFamily n t ht htn hcard ∧
      Module.finrank k B-Module.finrank k Q.radical=2*t ∧ v∈Q.radical := by
  simp only [traceHyperplaneRankFamily,traceRankFamily,Finset.mem_filter,and_assoc]
/-- The exact hyperplane radical-incidence identity for the concrete rank-2t trace subfamily. -/
theorem traceHyperplaneRankFamily_card_mul (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (v : B) (hv : v≠0) :
    (traceHyperplaneRankFamily n t ht htn hcard v).card*((Fintype.card k)^(2*n)-1)=
      (traceRankFamily n t ht htn hcard (2*t)).card*((Fintype.card k)^(2*n-2*t)-1) := by
  exact traceRankFamily_radical_incidence n t ht htn hcard (2*t) v hv
/-- A lower bound for the actual full-field rank population transfers with exactly the paper's hyperplane Gaussian correction. -/
theorem traceHyperplaneRankFamily_card_lower (n t : ℕ) (ht : 1≤t) (htn : t≤n)
    (hcard : Fintype.card B=(Fintype.card k)^(2*n)) (v : B) (hv : v≠0)
    (hpop : ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) n t≤
      (traceRankFamily n t ht htn hcard (2*t)).card) :
    ((Fintype.card k)^t-1)*gaussianPascal ((Fintype.card k)^2) (n-1) t≤
      (traceHyperplaneRankFamily n t ht htn hcard v).card := by
  have hq : 1<Fintype.card k := Fintype.one_lt_card
  have hQ : 1<(Fintype.card k)^2 := Nat.one_lt_pow (by omega) hq
  have hratio := gaussianPascal_dimension_ratio ((Fintype.card k)^2) n t hQ htn
  rw [←pow_mul,←pow_mul,show 2*(n-t)=2*n-2*t by omega] at hratio
  have hinc := traceHyperplaneRankFamily_card_mul n t ht htn hcard v hv
  have hden : 0<(Fintype.card k)^(2*n)-1 := by
    have hh : 1<(Fintype.card k)^(2*n) := Nat.one_lt_pow (by omega) hq
    omega
  have hmul := Nat.mul_le_mul_right ((Fintype.card k)^(2*n-2*t)-1) hpop
  rw [←hinc] at hmul
  have hr := congrArg (fun z => ((Fintype.card k)^t-1)*z) hratio
  nlinarith
end BinaryFieldCounterexamples.QuadraticFormTrace
