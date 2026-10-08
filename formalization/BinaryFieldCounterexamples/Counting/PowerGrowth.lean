/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.GaussianEstimates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Elementary closure laws for binary power growth

Positive two-sided constants quantify before the dimension. Fixed dimension
shifts, products and positive multipliers preserve this explicit uniform contract.
-/
@[expose] public section

namespace BinaryFieldCounterexamples
/-- Positive two-sided bounds by a fixed power of the binary domain size. -/
def HasBinaryPowerGrowth (f : ℕ → ℕ) (e : ℕ) : Prop :=
  ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀≤d →
    c*(2^d:ℝ)^e ≤ f d ∧ (f d : ℝ) ≤ C*(2^d:ℝ)^e

/-- Growth exponents add under products. -/
theorem HasBinaryPowerGrowth.mul {f g : ℕ → ℕ} {e k : ℕ}
    (hf : HasBinaryPowerGrowth f e) (hg : HasBinaryPowerGrowth g k) :
    HasBinaryPowerGrowth (fun d => f d*g d) (e+k) := by
  obtain ⟨c,C,hc,hC,d₀,hf⟩ := hf
  obtain ⟨b,B,hb,hB,n₀,hg⟩ := hg
  refine ⟨c*b,C*B,mul_pos hc hb,mul_pos hC hB,max d₀ n₀,?_⟩
  intro d hd
  obtain ⟨hfl,hfu⟩ := hf d ((le_max_left _ _).trans hd)
  obtain ⟨hgl,hgu⟩ := hg d ((le_max_right _ _).trans hd)
  rw [Nat.cast_mul]
  constructor
  · calc
      _ = (c*(2^d:ℝ)^e)*(b*(2^d:ℝ)^k) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul hfl hgl (by positivity) (by positivity)
  · calc
      _ ≤ (C*(2^d:ℝ)^e)*(B*(2^d:ℝ)^k) := mul_le_mul hfu hgu (by positivity) (by positivity)
      _ = _ := by rw [pow_add]; ring

/-- A fixed positive natural multiplier preserves the exponent. -/
theorem HasBinaryPowerGrowth.const_mul {f : ℕ → ℕ} {e : ℕ}
    (hf : HasBinaryPowerGrowth f e) (A : ℕ) (hA : 0<A) :
    HasBinaryPowerGrowth (fun d => A*f d) e := by
  obtain ⟨c,C,hc,hC,d₀,hf⟩ := hf
  refine ⟨A*c,A*C,mul_pos (by exact_mod_cast hA) hc,
    mul_pos (by exact_mod_cast hA) hC,d₀,?_⟩
  intro d hd
  obtain ⟨hl,hu⟩ := hf d hd
  rw [Nat.cast_mul]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg A)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg A)

/-- A fixed dimension shift changes only the positive constants. -/
theorem HasBinaryPowerGrowth.shift {f : ℕ → ℕ} {e : ℕ}
    (hf : HasBinaryPowerGrowth f e) (s : ℕ) :
    HasBinaryPowerGrowth (fun d => f (d-s)) e := by
  obtain ⟨c,C,hc,hC,d₀,hf⟩ := hf
  refine ⟨c/(2^s:ℝ)^e,C/(2^s:ℝ)^e,by positivity,by positivity,d₀+s,?_⟩
  intro d hd
  have hsd : s≤d := by omega
  have hpow : (2:ℝ)^d=2^s*2^(d-s) := by
    rw [← pow_add]
    congr 1
    omega
  have heq (a : ℝ) : a/(2^s:ℝ)^e*(2^d:ℝ)^e = a*(2^(d-s):ℝ)^e := by
    rw [hpow,mul_pow]
    field_simp
  rw [heq,heq]
  exact hf (d-s) (by omega)

/-- Pointwise equality preserves the concrete two-sided bounds. -/
theorem HasBinaryPowerGrowth.congr {f g : ℕ → ℕ} {e : ℕ}
    (hf : HasBinaryPowerGrowth f e) (hfg : ∀d, f d=g d) : HasBinaryPowerGrowth g e := by
  have : f=g := funext hfg
  rwa [← this]

/-- The Gaussian quotient has exponent equal to its fixed lower dimension. -/
theorem gaussianBinomial_two_growth (r : ℕ) :
    HasBinaryPowerGrowth (fun n => gaussianBinomial 2 n r) r := by
  have hden : (0:ℝ)<binaryFrameProduct r r := by exact_mod_cast binaryFrameProduct_pos r r le_rfl
  refine ⟨(2^(r+1)*(binaryFrameProduct r r:ℝ))⁻¹,
    (binaryFrameProduct r r:ℝ)⁻¹,by positivity,by positivity,r,?_⟩
  intro n hn
  simpa only [div_eq_mul_inv,mul_comm] using gaussianBinomial_two_bounds n r hn
end BinaryFieldCounterexamples
