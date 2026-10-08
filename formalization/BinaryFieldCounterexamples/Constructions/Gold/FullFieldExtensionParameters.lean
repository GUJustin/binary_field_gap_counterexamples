/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionParameters
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-!
# Even-dimensional full-field Gold parameters

For length `N=2^(2*n)` and fixed extension degree `e`, the choice
`t=n-e+1` has collision multiplicity `4^(e-1)` and enough actual locators
for the sharp constant-probability consequence.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- The full-field list exceeds every fixed binary multiple of the challenge field. -/
theorem full_field_extension_list_ge_scaled_field (n e k : ℕ)
    (he : 2 ≤ e) (hn : e + 2 ≤ n) (hscale : 2*e^2+k+2 ≤ n) :
    2^k * (2^(2*n))^e ≤
      2^(2*(n-e+1))*(2^(n+e-1)-1)*gaussianBinomial 4 n (e-1) := by
  have hG := pow_mul_sub_le_gaussianBinomial 4 n (e-1) (by decide) (by omega)
  have hsub : 2^(n+e-2) ≤ 2^(n+e-1)-1 := by
    have hp : 2^(n+e-1)=2^(n+e-2)*2 := by
      rw [show n+e-1=(n+e-2)+1 by omega,pow_succ]
    rw [hp]
    have : 0<2^(n+e-2) := by positivity
    omega
  have hprod := Nat.mul_le_mul_left (2^(2*(n-e+1))) (Nat.mul_le_mul hsub hG)
  apply le_trans ?_ (by simpa only [Nat.mul_assoc] using hprod)
  rw [show n-(e-1)=n-e+1 by omega]
  rw [show 4=2^2 by norm_num,←pow_mul,←pow_mul,←pow_add,←pow_add,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hE : (e:ℤ)-1 = ((e-1:ℕ):ℤ) := by omega
  have hN : (n:ℤ)-(e:ℤ)+1 = ((n-e+1:ℕ):ℤ) := by omega
  have hNE : (n:ℤ)+(e:ℤ)-2 = ((n+e-2:ℕ):ℤ) := by omega
  have hs : 2*(e:ℤ)^2+(k:ℤ)+2≤(n:ℤ) := by exact_mod_cast hscale
  have hh : (k:ℤ)+2*(n:ℤ)*(e:ℤ) ≤
      2*((n-e+1:ℕ):ℤ)+((n+e-2:ℕ):ℤ)+2*(((e-1:ℕ):ℤ)*((n-e+1:ℕ):ℤ)) := by
    rw [←hE,←hN,←hNE]
    linarith
  have hhNat : k+2*n*e ≤ 2*(n-e+1)+(n+e-2)+2*((e-1)*(n-e+1)) := by
    exact_mod_cast hh
  simpa only [Nat.add_assoc] using hhNat

/-- The actual Gold locator population at the even full-field parameters. -/
theorem full_field_extension_list_eq (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    2^(2*(n-e+1)) *
      (2^(2*n-(n-e+1)*(2*n-2*n+if Even (2*n) then 1 else 0))-1) *
      gaussianBinomial 4 ((2*n)/2) (n-e+1) =
    2^(2*(n-e+1))*(2^(n+e-1)-1)*gaussianBinomial 4 n (e-1) := by
  have heven : Even (2*n) := ⟨n,by omega⟩
  rw [ite_eq_left heven]
  have hΔ : 2*n-(n-e+1)*(2*n-2*n+1)=n+e-1 := by
    simp only [Nat.sub_self,zero_add,mul_one]
    omega
  rw [hΔ,show 2*n/2=n by omega]
  rw [gaussianBinomial_symm 4 n (n-e+1) (by decide) (by omega)]
  congr 2
  omega

/-- Collision multiplicity stays constant as the full field grows. -/
theorem full_field_extension_delta_eq (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    2^(2*n)/2^(2*(n-e+1))=2^(2*(e-1)) := by
  rw [Nat.pow_div (by omega : 2*(n-e+1)≤2*n) (by decide)]
  congr 1
  omega

/-- Integer agreement threshold for the even full-field family. -/
theorem full_field_extension_threshold_eq (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    2^(2*n)/2-2^(2*n)/2^(n-e+1+1)=2^(2*n-1)-2^(n+e-2) := by
  have hhalf : 2^(2*n)/2=2^(2*n-1) := by
    simpa using Nat.pow_div (x:=2) (m:=2*n) (n:=1) (by omega) (by decide)
  rw [hhalf,Nat.pow_div (by omega : n-e+1+1≤2*n) (by decide)]
  congr 2
  omega

/-- The integer threshold is exactly the displayed full-field radical formula.
The exponent `e-2` is a natural exponent; `e≥2` ensures no truncation ambiguity. -/
theorem full_field_extension_threshold_eq_radical (n e : ℕ)
    (he : 2 ≤ e) (hn : e+2 ≤ n) :
    ((2^(2*n-1)-2^(n+e-2) : ℕ) : ℝ) =
      ((2^(2*n) : ℕ) : ℝ)/2 - (2:ℝ)^(e-2)*Real.sqrt (2^(2*n) : ℕ) := by
  have hsub : (2:ℕ)^(n+e-2) ≤ 2^(2*n-1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hhalf : ((2^(2*n) : ℕ) : ℝ)/2 = (2:ℝ)^(2*n-1) := by
    push_cast
    conv_lhs => rw [show 2*n = (2*n-1)+1 by omega, pow_succ]
    ring
  have hsqrt : Real.sqrt (2^(2*n) : ℕ) = (2:ℝ)^n := by
    push_cast
    rw [show 2*n = n*2 by omega, pow_mul, Real.sqrt_sq (by positivity)]
  rw [hhalf, hsqrt, ← pow_add, show e-2+n = n+e-2 by omega]
end BinaryFieldCounterexamples.Gold
