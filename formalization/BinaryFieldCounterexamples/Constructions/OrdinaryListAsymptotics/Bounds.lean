/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
/-!
# Explicit asymptotic constants for full-field decoding lists

The estimates are uniform over finite fields with fixed scalar cardinality.
The floor `t = n/2` loses only a bounded factor in the Johnson deficit and
keeps a quadratic exponent in the Gaussian population.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.OrdinaryListConstruction

/-- The exact integer agreement has its advertised normalized fraction. -/
theorem fullfield_agreement_fraction (b n t : ℕ) (hb : 2 ≤ b)
    (ht : 1 ≤ t) (htn : t ≤ n) :
    ((b^(2*n-1)-(b-1)*b^(2*n-t-1) : ℕ) : ℝ)/(b:ℝ)^(2*n) =
      1/(b:ℝ)-((b:ℝ)-1)/(b:ℝ)^(t+1) := by
  have hbpos : 0 < b := by omega
  have hmul : (b-1)*b^(2*n-t-1) ≤ b^(2*n-1) := by
    calc
      (b-1)*b^(2*n-t-1) ≤ b*b^(2*n-t-1) := Nat.mul_le_mul_right _ (by omega)
      _ = b^(2*n-t) := by rw [←pow_succ']; congr 1; omega
      _ ≤ b^(2*n-1) := Nat.pow_le_pow_right hbpos (by omega)
  rw [Nat.cast_sub hmul,Nat.cast_mul,Nat.cast_sub (by omega : 1≤b)]
  push_cast
  have h1 : (b:ℝ)^(2*n-1)*b=(b:ℝ)^(2*n) := by
    rw [←pow_succ]; congr 1; omega
  have h2 : (b:ℝ)^(2*n-t-1)*(b:ℝ)^(t+1)=(b:ℝ)^(2*n) := by
    rw [←pow_add]; congr 1; omega
  have hbR : (b:ℝ)≠0 := by positivity
  field_simp
  linarith [congrArg (fun x : ℝ => x*(b:ℝ)^(t+1)) h1,
    congrArg (fun x : ℝ => x*b*(b-1)) h2]

/-- A middle-rank Gaussian power has a uniform positive logarithmic list exponent. -/
theorem middle_rank_power_superpolynomial (b n : ℕ) (hb : 2 ≤ b) (hn : 4 ≤ n) :
    ((b:ℝ)^(2*n))^((1/(32*Real.log b))*Real.log ((b:ℝ)^(2*n))) ≤
      (b:ℝ)^(2*(n/2)*(n-n/2)) := by
  have hbR : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have hlog : 0<Real.log b := Real.log_pos hbR
  have hn4 : n ≤ 4*(n/2) := by omega
  have ht : n/2 ≤ n-n/2 := by omega
  have hsq : n^2 ≤ 16*(n/2)^2 := by nlinarith
  have hprod := Nat.mul_le_mul_left (n/2) ht
  have hexp : (n:ℝ)^2 ≤ 8*((2*(n/2)*(n-n/2):ℕ):ℝ) := by
    exact_mod_cast (show n^2 ≤ 8*(2*(n/2)*(n-n/2)) by linarith)
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow]
  have hp : (b:ℝ)^(2*(n/2)*(n-n/2))=
      Real.exp (((2*(n/2)*(n-n/2):ℕ):ℝ)*Real.log b) := by
    rw [←Real.log_pow,Real.exp_log (by positivity)]
  rw [hp]
  apply Real.exp_le_exp.mpr
  push_cast
  have he : ((2:ℝ)*n*Real.log b)*((1/(32*Real.log b))*((2:ℝ)*n*Real.log b)) =
      (n:ℝ)^2/8*Real.log b := by field_simp; ring
  rw [he]
  push_cast at hexp
  exact mul_le_mul_of_nonneg_right (by linarith) hlog.le

/-- The floor in the middle rank gives two explicit positive fourth-root constants. -/
theorem middle_rank_deficit_bounds (b n : ℕ) (hb : 2 ≤ b) :
    (((b:ℝ)-1)/b)*((b:ℝ)^(2*n))^(-(1/4:ℝ)) ≤
        ((b:ℝ)-1)/(b:ℝ)^(n/2+1) ∧
    ((b:ℝ)-1)/(b:ℝ)^(n/2+1) ≤
        ((b:ℝ)-1)*((b:ℝ)^(2*n))^(-(1/4:ℝ)) := by
  have hbR : (1:ℝ)<b := by exact_mod_cast (show 1<b by omega)
  have hbpos : (0:ℝ)<b := by linarith
  have hroot : ((b:ℝ)^(2*n))^(-(1/4:ℝ))=(b:ℝ)^(-(n:ℝ)/2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hbpos.le]
    congr 1
    push_cast
    ring
  rw [hroot]
  have hlow : (n:ℝ)/2 ≤ (n/2:ℕ)+1 := by
    have h : n ≤ 2*(n/2+1) := by omega
    have h' : (n:ℝ) ≤ 2*((n/2:ℕ)+1) := by exact_mod_cast h
    linarith
  have hupp : ((n/2:ℕ):ℝ) ≤ (n:ℝ)/2 := by
    have h : 2*(n/2) ≤ n := by omega
    have h' : 2*((n/2:ℕ):ℝ) ≤ n := by exact_mod_cast h
    linarith
  have hratio : ((b:ℝ)-1)/(b:ℝ)^(n/2+1)=
      ((b:ℝ)-1)*(b:ℝ)^(-((n/2:ℕ)+1:ℝ)) := by
    rw [Real.rpow_neg hbpos.le,Real.rpow_add_one hbpos.ne',Real.rpow_natCast,pow_succ]
    rfl
  rw [hratio]
  constructor
  · have hpower : (b:ℝ)^(-(n:ℝ)/2-1) ≤ (b:ℝ)^(-((n/2:ℕ)+1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbR.le (by linarith)
    have hid : (((b:ℝ)-1)/b)*(b:ℝ)^(-(n:ℝ)/2)=
        ((b:ℝ)-1)*(b:ℝ)^(-(n:ℝ)/2-1) := by
      rw [Real.rpow_sub hbpos,Real.rpow_one]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hpower (by linarith)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbR.le (by linarith)) (by linarith)
end BinaryFieldCounterexamples.OrdinaryListConstruction
