/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.CollisionSaturation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Numerical arbitrary-rate pooling bounds

The literal rational ceiling estimate implies the required real probability
bound after removing at most challenge zero. Polynomial family growth of
exponent `s>2a` also exceeds the exact finite saturation threshold uniformly
for field sizes at most `N^a`; the resulting ceiling equals the field size.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Filter
/-- The exact rational ceiling pooling bound implies the real arbitrary-rate
probability estimate, including the possible removal of challenge zero. -/
theorem allRate_probability_bound (q N M b b0 s : ℕ) (C : ℝ)
    (hq : 0<q) (hN : 0<N) (hM : 0<M) (hC : 0<C)
    (hpopulation : (N:ℝ)^s/C≤M)
    (hb : ⌈((q*M:ℕ):ℚ)/(q+M-1:ℕ)⌉₊≤b) (hb0 : b≤b0+1) :
    1/(1+C*q/(N:ℝ)^s)-1/q≤(b0:ℝ)/q := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  have hNR : (0:ℝ)<(N:ℝ)^s := pow_pos (by exact_mod_cast hN) _
  have hden : (0:ℝ)<q+M-1 := by
    have : (1:ℝ)≤q := by exact_mod_cast hq
    linarith
  have hratioQ := Nat.ceil_le.mp hb
  have hratio : (q:ℝ)*M/(q+M-1)≤b := by
    have hc := (Rat.cast_le (K:=ℝ)).2 hratioQ
    norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,Rat.cast_one,Nat.cast_mul,
      Nat.cast_sub (show 1≤q+M by omega),Nat.cast_add,Nat.cast_one] at hc
    exact hc
  have hpop : (N:ℝ)^s≤C*M := by
    have := (div_le_iff₀ hC).mp hpopulation
    linarith
  have hbase : 1/(1+C*q/(N:ℝ)^s)≤(M:ℝ)/(q+M) := by
    have hd : 0<1+C*q/(N:ℝ)^s := by positivity
    apply (div_le_div_iff₀ hd (by positivity)).mpr
    field_simp
    linarith [mul_le_mul_of_nonneg_right hpop hqR.le]
  have hratio' : (M:ℝ)/(q+M)≤(b:ℝ)/q := by
    apply (div_le_div_iff₀ (by positivity) hqR).mpr
    have hh := (div_le_iff₀ hden).mp hratio
    have hbR : (0:ℝ)≤b := by positivity
    linarith
  have hb0R : (b:ℝ)≤b0+1 := by exact_mod_cast hb0
  have hloss : (b:ℝ)/q-1/q≤(b0:ℝ)/q := by
    rw [←sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hqR.le
  exact (sub_le_sub_right (hbase.trans hratio') _).trans hloss
/-- A population of order `N^s` eventually exceeds the exact saturation
threshold uniformly for every field size at most `N^a`, when `s>2a`. -/
theorem allRate_eventual_saturation_population (a C : ℝ) (s : ℕ)
    (hC : 0<C) (hs : 2*a<s) :
    ∃ N1 : ℕ, 1≤N1 ∧ ∀ N : ℕ, N1≤N → ∀ q M : ℕ,
      (q:ℝ)≤(N:ℝ)^a → (N:ℝ)^s/C≤M → (q-1)^2<M := by
  have hg : 0<(s:ℝ)-2*a := by linarith
  obtain ⟨R,hR⟩ := tendsto_atTop_atTop.mp (tendsto_rpow_atTop hg) (C+1)
  obtain ⟨N1,hN1⟩ := exists_nat_ge (max R 1)
  have hN11 : 1≤N1 := by
    have : (1:ℝ)≤N1 := (le_max_right R 1).trans hN1
    exact_mod_cast this
  refine ⟨N1,hN11,?_⟩
  intro N hN q M hq hM
  have hNcast : (N1:ℝ)≤N := by exact_mod_cast hN
  have hNR : (0:ℝ)<N := by
    have : 1≤N := hN11.trans hN
    exact_mod_cast (show 0<N by omega)
  have hlarge : C<(N:ℝ)^((s:ℝ)-2*a) := by
    have := hR (N:ℝ) ((le_max_left R 1).trans hN1 |>.trans hNcast)
    linarith
  have hp : 0<(N:ℝ)^(2*a) := Real.rpow_pos_of_pos hNR _
  have he : (N:ℝ)^(2*a)*(N:ℝ)^((s:ℝ)-2*a)=(N:ℝ)^s := by
    rw [←Real.rpow_add hNR]
    rw [show 2*a+((s:ℝ)-2*a)=(s:ℝ) by ring,Real.rpow_natCast]
  have hsmall : (N:ℝ)^(2*a)<(N:ℝ)^s/C := by
    apply (lt_div_iff₀ hC).mpr
    have := mul_lt_mul_of_pos_left hlarge hp
    rw [he] at this
    linarith
  have hsq : (q:ℝ)^2≤(N:ℝ)^(2*a) := by
    have hq0 : (0:ℝ)≤q := by positivity
    have hh : (q:ℝ)^2≤((N:ℝ)^a)^2 := by nlinarith
    have he' : ((N:ℝ)^a)^2=(N:ℝ)^(2*a) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hNR.le]
      congr 1
      norm_num
      ring
    rwa [he'] at hh
  have hsub : (((q-1:ℕ):ℝ))^2≤(q:ℝ)^2 := by
    have hle : ((q-1:ℕ):ℝ)≤q := by exact_mod_cast Nat.sub_le q 1
    have hnn : (0:ℝ)≤((q-1:ℕ):ℝ) := by positivity
    nlinarith
  have hfinal := hsub.trans hsq |>.trans_lt (hsmall.trans_le hM)
  exact_mod_cast hfinal
/-- Removing at most one image value preserves the explicit probability bound. -/
theorem allRate_probability_bound_pred (q N M b s : ℕ) (C : ℝ)
    (hq : 0<q) (hN : 0<N) (hM : 0<M) (hC : 0<C)
    (hpopulation : (N:ℝ)^s/C≤M)
    (hb : ⌈((q*M:ℕ):ℚ)/(q+M-1:ℕ)⌉₊≤b) :
    1/(1+C*q/(N:ℝ)^s)-1/q≤((b-1:ℕ):ℝ)/q := by
  exact allRate_probability_bound q N M b (b-1) s C hq hN hM hC hpopulation hb (by omega)
/-- The eventual population bound forces the literal rational pooling ceiling
to equal the whole field size, with no subtraction of zero. -/
theorem allRate_eventual_pooling_ceil_eq_field_size (a C : ℝ) (s : ℕ)
    (hC : 0<C) (hs : 2*a<s) :
    ∃ N1 : ℕ, 1≤N1 ∧ ∀ N : ℕ, N1≤N → ∀ q M : ℕ, 0<q →
      (q:ℝ)≤(N:ℝ)^a → (N:ℝ)^s/C≤M →
      ⌈((q*M:ℕ):ℚ)/(q+M-1:ℕ)⌉₊=q := by
  obtain ⟨N1,hN1,h⟩ := allRate_eventual_saturation_population a C s hC hs
  refine ⟨N1,hN1,?_⟩
  intro N hN q M hq hsize hpop
  have hM := h N hN q M hsize hpop
  have he := collision_pooling_ceil_eq_field_size q M hq hM
  have hden : 1≤q+M := by omega
  simpa only [Nat.cast_mul,Nat.cast_sub hden,Nat.cast_add,Nat.cast_one] using he
end BinaryFieldCounterexamples
