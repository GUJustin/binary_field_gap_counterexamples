/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.EnergyLowerBound
/-! # Explicit deficit from the fixed-extension Gold probability

The exact finite collision quotient approaches `1/δ` with three displayed
errors. No asymptotic estimate or change of the paper's leading coefficient is
assumed. The natural ceiling and deletion of one challenge are kept.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
set_option autoImplicit false
/-- The exact Gold count divided by q is at least the leading coefficient
1/δ minus explicit domain, list-size and rounding deficits. -/
theorem gold_energy_probability_deficit (N δ L q : ℕ)
    (hNq : N<q) (hδ : 0<δ) (hL : 0<L) :
    let Z : ℕ := ⌈(L:ℚ)*((q:ℚ)-(N:ℚ)) /
      ((q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1))⌉₊-1
    (1:ℚ)/(δ:ℚ) - (N:ℚ)/((δ:ℚ)*(q:ℚ)) -
      (q:ℚ)/((δ:ℚ)^2*(L:ℚ)) - 1/(q:ℚ) ≤ (Z:ℚ)/(q:ℚ) := by
  have hq : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have hd : (0:ℚ)<δ := by exact_mod_cast hδ
  have hl : (0:ℚ)<L := by exact_mod_cast hL
  have hl1 : (1:ℚ)≤L := by exact_mod_cast hL
  have hnq : (N:ℚ)<q := by exact_mod_cast hNq
  have hn : (0:ℚ)≤N := by positivity
  have hden : (0:ℚ)<(q:ℚ)-N+(δ:ℚ)*((L:ℚ)-1) := by positivity
  have hbig : (0:ℚ)<(q:ℚ)+(δ:ℚ)*L := by positivity
  let x : ℚ := (L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+(δ:ℚ)*((L:ℚ)-1))
  have hnum : (0:ℚ)<(L:ℚ)*((q:ℚ)-N) := mul_pos hl (sub_pos.mpr hnq)
  have hsmall : (L:ℚ)*((q:ℚ)-N)/((q:ℚ)+(δ:ℚ)*L)≤x := by
    apply div_le_div_of_nonneg_left hnum.le hden
    linarith
  let r : ℚ := (N:ℚ)/q
  let s : ℚ := (q:ℚ)/((δ:ℚ)*L)
  have hr : 0≤r := by dsimp [r];positivity
  have hs : 0≤s := by dsimp [s];positivity
  have helem : 1-r-s≤(1-r)/(1+s) := by
    rw [le_div_iff₀ (by linarith : 0<1+s)]
    linarith [mul_nonneg hr hs,sq_nonneg s]
  have hpre : (1:ℚ)/δ-(N:ℚ)/((δ:ℚ)*q)-(q:ℚ)/((δ:ℚ)^2*L) ≤
      ((L:ℚ)*((q:ℚ)-N)/((q:ℚ)+(δ:ℚ)*L))/(q:ℚ) := by
    calc
      _=(1-r-s)/(δ:ℚ) := by dsimp [r,s];field_simp
      _≤((1-r)/(1+s))/(δ:ℚ) := div_le_div_of_nonneg_right helem hd.le
      _=_ := by dsimp [r,s];field_simp;ring
  have hprex : (1:ℚ)/δ-(N:ℚ)/((δ:ℚ)*q)-(q:ℚ)/((δ:ℚ)^2*L)≤x/(q:ℚ) :=
    hpre.trans (div_le_div_of_nonneg_right hsmall hq.le)
  have hx : 0<x := div_pos hnum hden
  have hceil : 1≤⌈x⌉₊ := Nat.ceil_pos.mpr hx
  have hround : x-1≤((⌈x⌉₊-1:ℕ):ℚ) := by
    rw [Nat.cast_sub hceil,Nat.cast_one]
    exact sub_le_sub_right (Nat.le_ceil x) 1
  change _≤((⌈x⌉₊-1:ℕ):ℚ)/(q:ℚ)
  calc
    _≤x/(q:ℚ)-1/(q:ℚ) := sub_le_sub_right hprex _
    _=(x-1)/(q:ℚ) := by ring
    _≤_ := div_le_div_of_nonneg_right hround hq.le
end BinaryFieldCounterexamples.Gold
