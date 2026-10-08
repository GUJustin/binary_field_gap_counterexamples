/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Native128Certificate
public import BinaryFieldCounterexamples.Constructions.Longfellow.Arithmetic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Exact two-sided decimal certificates in Section 5.7--5.9

The displayed decimals are certified as rational intervals. Logarithm
intervals use the finite Taylor estimate for `log((1+x)/(1-x))`, avoiding
large integer powers at decimal denominators. Every calculation is
kernel-checked. Table 6's Johnson percentages round to 37.8 percent,
correcting the paper's prose value of 37.7 percent.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 100000

def logTaylor (x : ℚ) (n : ℕ) : ℚ :=
  2*∑i∈Finset.range n,x^(2*i+1)/((2*i+1:ℕ):ℚ)

theorem log_interval_of_taylor (x lo hi : ℚ) (n : ℕ)
    (hx : 0≤x) (hx1 : x<1)
    (hl : lo<logTaylor x n)
    (hu : logTaylor x n+2*x^(2*n+1)/(1-x^2)<hi) :
    (lo:ℝ)<Real.log ((1+(x:ℝ))/(1-(x:ℝ))) ∧
      Real.log ((1+(x:ℝ))/(1-(x:ℝ)))<(hi:ℝ) := by
  have hlo:=Real.sum_range_le_log_div (x:=(x:ℝ)) (by exact_mod_cast hx) (by exact_mod_cast hx1) n
  have hup:=Real.log_div_le_sum_range_add (x:=(x:ℝ)) (by exact_mod_cast hx) (by exact_mod_cast hx1) n
  have hlR : (lo:ℝ)<(logTaylor x n:ℝ):=by exact_mod_cast hl
  have huR : (logTaylor x n:ℝ)+2*(x:ℝ)^(2*n+1)/(1-(x:ℝ)^2)<(hi:ℝ):=by exact_mod_cast hu
  simp only [logTaylor,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_sum,Rat.cast_div,
    Rat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hlR huR
  push_cast at hlR huR
  simp only [mul_div_assoc] at huR
  constructor <;> linarith

theorem log_two_interval :
    (69314718055994/10^14:ℝ)<Real.log 2 ∧
      Real.log 2<(69314718055995/10^14:ℝ) := by
  have h:=log_interval_of_taylor (1/3) (69314718055994/10^14) (69314718055995/10^14) 15
    (by norm_num) (by norm_num) (by norm_num [logTaylor,Finset.sum_range_succ])
    (by norm_num [logTaylor,Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem native_ratio_log_interval :
    (77594750318918/10^15:ℝ)<Real.log ((342482627693920113354525730019:ℝ)/2^98) ∧
      Real.log ((342482627693920113354525730019:ℝ)/2^98)<(77594750318920/10^15:ℝ) := by
  let x:ℚ:=(342482627693920113354525730019-2^98)/(342482627693920113354525730019+2^98)
  have h:=log_interval_of_taylor x (77594750318918/10^15) (77594750318920/10^15) 5
    (by norm_num [x]) (by norm_num [x]) (by norm_num [x,logTaylor,Finset.sum_range_succ])
    (by norm_num [x,logTaylor,Finset.sum_range_succ])
  have he : (1+(x:ℝ))/(1-(x:ℝ))=(342482627693920113354525730019:ℝ)/2^98 := by
    norm_num [x]
  rw [he] at h
  norm_num at h ⊢
  exact h

theorem longfellow_ratio_log_interval :
    (331581297652249/10^15:ℝ)<Real.log ((5843376:ℝ)/2^22) ∧
      Real.log ((5843376:ℝ)/2^22)<(331581297652251/10^15:ℝ) := by
  let x:ℚ:=(5843376-2^22)/(5843376+2^22)
  have h:=log_interval_of_taylor x (331581297652249/10^15) (331581297652251/10^15) 10
    (by norm_num [x]) (by norm_num [x]) (by norm_num [x,logTaylor,Finset.sum_range_succ])
    (by norm_num [x,logTaylor,Finset.sum_range_succ])
  have he : (1+(x:ℝ))/(1-(x:ℝ))=(5843376:ℝ)/2^22 := by norm_num [x]
  rw [he] at h
  norm_num at h ⊢
  exact h

/-- Corollary 5.18's proof: the exact padding retention lies in a rational
interval confirming all ten displayed decimal places of `0.9922399879`. -/
theorem native128_retention_decimal :
    (99223998789/10^11:ℚ)<paddingRetentionProbability 27 19 12 ∧
      paddingRetentionProbability 27 19 12<(99223998791/10^11:ℚ) := by
  rw [paddingRetentionProbability_product 27 19 12 (by decide) (by decide)]
  norm_num [Finset.prod_range_succ]

/-- Corollary 5.18's proof: the exact retained-count probability exponent
is strictly between `29.888054438` and `29.888054439`. -/
theorem native128_probability_exponent_decimal :
    (29888054438/10^9:ℝ)<128-Real.log (Gold.nativeGoldPaddedCountSharp:ℝ)/Real.log 2 ∧
      128-Real.log (Gold.nativeGoldPaddedCountSharp:ℝ)/Real.log 2<(29888054439/10^9:ℝ) := by
  rw [Gold.nativeGoldPaddedCountSharp_value]
  norm_num only [Nat.cast_ofNat]
  have hlog:=log_two_interval
  have hratio:=native_ratio_log_interval
  have h2pos : 0<Real.log 2:=Real.log_pos (by norm_num)
  have he : Real.log (342482627693920113354525730019:ℝ)=
      98*Real.log 2+Real.log ((342482627693920113354525730019:ℝ)/2^98) := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_pow]
    ring
  rw [he]
  have hl : (111945561/10^9:ℝ)<Real.log ((342482627693920113354525730019:ℝ)/2^98)/Real.log 2 := by
    apply (lt_div_iff₀ h2pos).mpr
    nlinarith
  have hu : Real.log ((342482627693920113354525730019:ℝ)/2^98)/Real.log 2<(111945562/10^9:ℝ) := by
    apply (div_lt_iff₀ h2pos).mpr
    nlinarith
  have hcancel : (98*Real.log 2+Real.log ((342482627693920113354525730019:ℝ)/2^98))/Real.log 2=
      98+Real.log ((342482627693920113354525730019:ℝ)/2^98)/Real.log 2 := by field_simp
  rw [hcancel]
  constructor <;> linarith

/-- Corollary 5.19's proof: the exact Longfellow-list probability exponent
is strictly between `105.521629` and `105.521630`. -/
theorem longfellow_probability_exponent_decimal :
    (105521629/10^6:ℝ)<128-Real.log (Longfellow.listSize:ℝ)/Real.log 2 ∧
      128-Real.log (Longfellow.listSize:ℝ)/Real.log 2<(105521630/10^6:ℝ) := by
  rw [Longfellow.listSize_value]
  norm_num only [Nat.cast_ofNat]
  have hlog:=log_two_interval
  have hratio:=longfellow_ratio_log_interval
  have h2pos : 0<Real.log 2:=Real.log_pos (by norm_num)
  have he : Real.log (5843376:ℝ)=22*Real.log 2+Real.log ((5843376:ℝ)/2^22) := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_pow]
    ring
  rw [he]
  have hl : (478370/10^6:ℝ)<Real.log ((5843376:ℝ)/2^22)/Real.log 2 := by
    apply (lt_div_iff₀ h2pos).mpr
    nlinarith
  have hu : Real.log ((5843376:ℝ)/2^22)/Real.log 2<(478371/10^6:ℝ) := by
    apply (div_lt_iff₀ h2pos).mpr
    nlinarith
  have hcancel : (22*Real.log 2+Real.log ((5843376:ℝ)/2^22))/Real.log 2=
      22+Real.log ((5843376:ℝ)/2^22)/Real.log 2 := by field_simp
  rw [hcancel]
  constructor <;> linarith

/-- Section 5.7: the native example is within the rounding intervals for
`0.58` percentage points below Johnson and `24.42` above common agreement. -/
theorem native128_percentage_gaps :
    (575/1000:ℚ)<100*(1/2-16193/32768:ℚ) ∧
      100*(1/2-16193/32768:ℚ)<585/1000 ∧
    (24415/1000:ℚ)<100*(16193/32768-1/4:ℚ) ∧
      100*(16193/32768-1/4:ℚ)<24425/1000 := by norm_num

/-- Table 6: each displayed combination-agreement percentage lies strictly
inside its two-decimal rounding interval, for all four actual parameter rows. -/
theorem longfellow_table_percentages :
    (26155/1000:ℚ)<100*(845/3230:ℚ) ∧ 100*(845/3230:ℚ)<26165/1000 ∧
    (25855/1000:ℚ)<100*(858/3318:ℚ) ∧ 100*(858/3318:ℚ)<25865/1000 ∧
    (25715/1000:ℚ)<100*(862/3352:ℚ) ∧ 100*(862/3352:ℚ)<25725/1000 ∧
    (25435/1000:ℚ)<100*(874/3436:ℚ) ∧ 100*(874/3436:ℚ)<25445/1000 := by norm_num

/-- Section 5.8's `14.3%` common agreement and `57.1%` unique-decoding
agreement are certified by two-sided rounding intervals for every Table 6 row. -/
theorem longfellow_common_unique_percentages (N K : ℕ)
    (h : (N,K)∈Longfellow.parameterPairs) :
    (1425/100:ℚ)<100*(K:ℚ)/N ∧ 100*(K:ℚ)/N<(1435/100:ℚ) ∧
    (5705/100:ℚ)<50*(1+(K:ℚ)/N) ∧ 50*(1+(K:ℚ)/N)<(5715/100:ℚ) := by
  simp only [Longfellow.parameterPairs,Finset.mem_insert,Finset.mem_singleton,
    Prod.mk.injEq] at h
  rcases h with h|h|h|h
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals norm_num

theorem sqrt_interval (q l u : ℚ) (hl : 0≤l) (hq : 0≤q)
    (hlq : l^2<q) (hqu : q<u^2) (hu : 0<u) :
    (l:ℝ)<Real.sqrt (q:ℝ) ∧ Real.sqrt (q:ℝ)<(u:ℝ) := by
  have hsq:=Real.sq_sqrt (x := (q:ℝ)) (by exact_mod_cast hq)
  have hnonneg:=Real.sqrt_nonneg (q:ℝ)
  have hlR : (0:ℝ)≤l:=by exact_mod_cast hl
  have huR : (0:ℝ)<u:=by exact_mod_cast hu
  have hlqR : (l:ℝ)^2<(q:ℝ):=by exact_mod_cast hlq
  have hquR : (q:ℝ)<(u:ℝ)^2:=by exact_mod_cast hqu
  constructor <;> nlinarith

/-- Section 5.8 and the introduction: all four Johnson agreements lie
between `37.75%` and `37.85%`, so round to `37.8%`, correcting the printed `37.7%`. -/
theorem longfellow_johnson_percentages (N K : ℕ)
    (h : (N,K)∈Longfellow.parameterPairs) :
    (3775/100:ℝ)<100*Real.sqrt ((K:ℝ)/N) ∧
      100*Real.sqrt ((K:ℝ)/N)<(3785/100:ℝ) := by
  have hboth : (3775/10000:ℚ)^2<(K:ℚ)/N ∧ (K:ℚ)/N<(3785/10000:ℚ)^2 := by
    simp only [Longfellow.parameterPairs,Finset.mem_insert,Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with h|h|h|h
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals norm_num
  have hsq:=sqrt_interval ((K:ℚ)/N) (3775/10000) (3785/10000) (by norm_num)
    (by positivity) hboth.1 hboth.2 (by norm_num)
  norm_num only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hsq
  constructor <;> linarith

/-- Section 5.8's `about 12 percentage points` loss below Johnson: every
Table 6 configuration has a loss strictly between `11.5` and `12.5` points. -/
theorem longfellow_johnson_gap_percentages (N K : ℕ)
    (h : (N,K)∈Longfellow.parameterPairs) :
    (115/10:ℝ) < 100*Real.sqrt ((K:ℝ)/N)-100*((K:ℝ)+384)/N ∧
      100*Real.sqrt ((K:ℝ)/N)-100*((K:ℝ)+384)/N < (125/10:ℝ) := by
  obtain ⟨hl,hu⟩ := longfellow_johnson_percentages N K h
  simp only [Longfellow.parameterPairs,Finset.mem_insert,Finset.mem_singleton,
    Prod.mk.injEq] at h
  rcases h with h|h|h|h
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals constructor <;> norm_num at * <;> linarith

/-- The comparison after Corollary 5.23: the binary Gold factor is at least
the elliptic factor at matched rank, and is strictly larger when `t<n`. -/
theorem binary_gold_elliptic_factor_comparison (n t : ℕ) (ht : t≤n) :
    2^t-1≤2^(2*n-t)-1 ∧ (t<n→2^t-1<2^(2*n-t)-1) := by
  have hexp : t≤2*n-t:=by omega
  have hle:=Nat.pow_le_pow_right (by decide : 0<2) hexp
  refine ⟨Nat.sub_le_sub_right hle 1,?_⟩
  intro htn
  have hexp' : t<2*n-t:=by omega
  have hlt:=Nat.pow_lt_pow_right (by decide : 1<2) hexp'
  have hp : 1≤2^t:=Nat.one_le_pow _ _ (by decide)
  omega

end BinaryFieldCounterexamples
