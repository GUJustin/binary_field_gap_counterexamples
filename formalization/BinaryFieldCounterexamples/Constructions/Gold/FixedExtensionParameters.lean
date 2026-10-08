/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianLowerBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-!
# Finite parameters for fixed extension degree

The odd-dimensional hyperplane choice `d=2*n-1`, `t=n-e` keeps the
collision parameter equal to `2^(2*e-1)`. The Gaussian leading-power
bound makes the locator population arbitrarily larger than the challenge
field for fixed `e`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- The fixed-extension locator population exceeds any specified binary
multiple of the challenge field once the displayed finite cutoff holds. -/
theorem fixed_extension_list_ge_scaled_field (n e k : ℕ)
    (he : 2≤e) (hn : e+2≤n)
    (hscale : 2*e^2+k+1≤n+e) :
    2^k*(2^(2*n))^e ≤
      2^(2*(n-e))*(2^(n+e)-1)*gaussianBinomial 4 (n-1) (e-1) := by
  have hG : 4^((e-1)*((n-1)-(e-1)))≤gaussianBinomial 4 (n-1) (e-1) :=
    pow_mul_sub_le_gaussianBinomial 4 (n-1) (e-1) (by decide) (by omega)
  have hsub : 2^(n+e-1)≤2^(n+e)-1 := by
    have hexp : n+e=(n+e-1)+1 := by omega
    have hp : 2^(n+e)=2^(n+e-1)*2 := by
      conv_lhs => rw [hexp,pow_succ]
    rw [hp]
    have : 0<2^(n+e-1) := by positivity
    omega
  have hprod := Nat.mul_le_mul_left (2^(2*(n-e))) (Nat.mul_le_mul hsub hG)
  apply le_trans ?_ (by simpa only [Nat.mul_assoc] using hprod)
  rw [show (n-1)-(e-1)=n-e by omega]
  rw [show 4=2^2 by norm_num,←pow_mul,←pow_mul,←pow_add,←pow_add,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hne : e≤n := by omega
  have hE : (e:ℤ)-1 = ((e-1:ℕ):ℤ) := by omega
  have hN : (n:ℤ)-(e:ℤ) = ((n-e:ℕ):ℤ) := by omega
  have hNE : (n:ℤ)+(e:ℤ)-1 = ((n+e-1:ℕ):ℤ) := by omega
  have hs : 2*(e:ℤ)^2+(k:ℤ)+1≤(n:ℤ)+(e:ℤ) := by exact_mod_cast hscale
  have hh : (k:ℤ)+2*(n:ℤ)*(e:ℤ) ≤
      2*((n-e:ℕ):ℤ)+((n+e-1:ℕ):ℤ)+2*(((e-1:ℕ):ℤ)*((n-e:ℕ):ℤ)) := by
    rw [←hE,←hN,←hNE]
    linarith
  have hhNat : k+2*n*e≤2*(n-e)+(n+e-1)+2*((e-1)*(n-e)) := by exact_mod_cast hh
  simpa only [Nat.add_assoc] using hhNat

/-- Odd hyperplane dimensions give the manuscript's explicit list parameter. -/
theorem fixed_extension_list_eq (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    2^(2*(n-e)) *
      (2^(2*n-(n-e)*(2*n-(2*n-1)+if Even (2*n-1) then 1 else 0))-1) *
      gaussianBinomial 4 ((2*n-1)/2) (n-e) =
    2^(2*(n-e))*(2^(n+e)-1)*gaussianBinomial 4 (n-1) (e-1) := by
  have hodd : ¬Even (2*n-1) := by
    rintro ⟨r,hr⟩
    omega
  rw [ite_eq_right hodd]
  have hΔ : 2*n-(n-e)*(2*n-(2*n-1)+0)=n+e := by
    rw [show 2*n-(2*n-1)+0=1 by omega,mul_one]
    omega
  rw [hΔ,show (2*n-1)/2=n-1 by omega]
  rw [gaussianBinomial_symm 4 (n-1) (n-e) (by decide) (by omega)]
  congr 2
  omega

/-- The collision parameter is independent of the growing domain length. -/
theorem fixed_extension_delta_eq (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    2^(2*n-1)/2^(2*(n-e))=2^(2*e-1) := by
  rw [Nat.pow_div (by omega : 2*(n-e)≤2*n-1) (by decide)]
  congr 1
  omega

/-- The agreement threshold in integer coordinates. -/
theorem fixed_extension_threshold_eq (n e : ℕ) (he : 2≤e) (hn : e+2≤n) :
    2^(2*n-1)/2-2^(2*n-1)/2^(n-e+1) =
      2^(2*n-2)-2^(n+e-2) := by
  have hhalf : 2^(2*n-1)/2=2^(2*n-2) := by
    have h := Nat.pow_div (x:=2) (m:=2*n-1) (n:=1) (by omega) (by decide)
    simpa only [pow_one,show 2*n-1-1=2*n-2 by omega] using h
  rw [hhalf,Nat.pow_div (by omega : n-e+1≤2*n-1) (by decide)]
  congr 2
  omega

end BinaryFieldCounterexamples.Gold
