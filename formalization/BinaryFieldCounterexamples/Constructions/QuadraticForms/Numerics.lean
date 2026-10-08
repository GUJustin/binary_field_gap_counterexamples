/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.QuadraticForms.SourceBound

/-!
# Numerical gap for the quadratic-form construction

The exact elliptic agreement threshold strictly exceeds the rational
prime-power bound on the first input's agreement throughout the theorem's parameter range.
-/

@[expose] public section

namespace BinaryFieldCounterexamples

/-- The prime-power first-input bound lies strictly below the elliptic agreement
threshold for every allowed rank parameter. -/
theorem primePowerQuarterSource_lt_ellipticAgreement
    (b d t N : ℕ) (hb : 2≤b) (hd : 3≤d) (ht : 2≤t) (htd : t+1≤d)
    (hN : N=b^d) :
    ((b+1:ℚ)*N/(2*b^2)-1) <
      (N/b-(b-1)*N/b^(t+1):ℕ) := by
  have hbpos : 0<b := by omega
  have hdiv1 : N/b=b^(d-1) := by
    rw [hN]
    simpa only [pow_one] using Nat.pow_div (show 1≤d by omega) hbpos
  have hdivt : (b-1)*N/b^(t+1)=(b-1)*b^(d-(t+1)) := by
    rw [hN,Nat.mul_div_assoc _ (pow_dvd_pow b htd),Nat.pow_div htd hbpos]
  have hsub : (b-1)*b^(d-(t+1))≤b^(d-1) := by
    calc
      (b-1)*b^(d-(t+1))≤b*b^(d-(t+1)) := Nat.mul_le_mul_right _ (by omega)
      _=b^(d-t) := by
        rw [←pow_succ']
        congr 1
        omega
      _≤b^(d-1) := Nat.pow_le_pow_right hbpos (by omega)
  rw [hdiv1,hdivt,Nat.cast_sub hsub,Nat.cast_mul,Nat.cast_sub (by omega : 1≤b)]
  have hpow : (b:ℚ)^d=(b:ℚ)^2*(b:ℚ)^(d-2) := by
    rw [←pow_add]
    congr 1
    omega
  have htbound : (b:ℚ)^(d-(t+1))≤(b:ℚ)^(d-3) := by
    apply pow_le_pow_right₀ (by exact_mod_cast (show 1≤b by omega)) (by omega)
  have hpow3 : (b:ℚ)^(d-2)=(b:ℚ)*(b:ℚ)^(d-3) := by
    rw [←pow_succ']
    congr 1
    omega
  have hpow1 : b^(d-1)=b^2*b^(d-3) := by
    rw [←pow_add]
    congr 1
    omega
  rw [hN,Nat.cast_pow,hpow,hpow3]
  rw [hpow1,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow]
  have hbq : (0:ℚ)<b := by exact_mod_cast hbpos
  have hbq2 : (2:ℚ)≤b := by exact_mod_cast hb
  have hb1 : (0:ℚ)≤(b:ℚ)-1 := by linarith
  simp only [Nat.cast_pow,Nat.cast_one] at *
  have hz2 : (2:ℚ)*(b:ℚ)^(d-(t+1))≤(b:ℚ)*(b:ℚ)^(d-3) := by
    calc
      (2:ℚ)*(b:ℚ)^(d-(t+1))≤2*(b:ℚ)^(d-3) :=
        mul_le_mul_of_nonneg_left htbound (by norm_num)
      _≤(b:ℚ)*(b:ℚ)^(d-3) :=
        mul_le_mul_of_nonneg_right hbq2 (by positivity)
  have hpnon : (0:ℚ)≤((b:ℚ)-1)*
      ((b:ℚ)*(b:ℚ)^(d-3)-2*(b:ℚ)^(d-(t+1))) :=
    mul_nonneg hb1 (sub_nonneg.mpr hz2)
  field_simp
  linarith

end BinaryFieldCounterexamples
