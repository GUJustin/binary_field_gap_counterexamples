/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
/-!
# Eventual domination by a larger binary power
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- A fixed larger real exponent eventually dominates a smaller real exponent,
while the underlying binary cardinality clears any prescribed natural bound. -/
theorem exists_binary_power_growth (b : ℝ) (e : ℕ) (hbe : b<(e:ℝ))
    (C : ℝ) (N₀ : ℕ) :
    ∃ d : ℕ, N₀≤2^d ∧
      C*(2:ℝ)^((d:ℝ)*b)<(2:ℝ)^((d:ℝ)*(e:ℝ)) := by
  let r : ℝ := (2:ℝ)^((e:ℝ)-b)
  have hr : 1<r := by
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr hbe)
  obtain ⟨d₁,hd₁⟩ := pow_unbounded_of_one_lt (N₀:ℝ) (by norm_num : (1:ℝ)<2)
  obtain ⟨d₂,hd₂⟩ := pow_unbounded_of_one_lt C hr
  let d := max d₁ d₂
  have hd₁d : d₁≤d := Nat.le_max_left _ _
  have hd₂d : d₂≤d := Nat.le_max_right _ _
  have hNreal : (N₀:ℝ)<(2:ℝ)^d := hd₁.trans_le (pow_le_pow_right₀ (by norm_num) hd₁d)
  have hN : N₀≤2^d := by exact_mod_cast hNreal.le
  have hCd : C<r^d := hd₂.trans_le (pow_le_pow_right₀ hr.le hd₂d)
  have hrform : r^d=(2:ℝ)^((d:ℝ)*((e:ℝ)-b)) := by
    rw [←Real.rpow_natCast]
    dsimp [r]
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hpow : C<(2:ℝ)^((d:ℝ)*((e:ℝ)-b)) := by rwa [←hrform]
  have hpos : 0<(2:ℝ)^((d:ℝ)*b) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨d,hN,?_⟩
  calc
    C*(2:ℝ)^((d:ℝ)*b)
        < (2:ℝ)^((d:ℝ)*((e:ℝ)-b))*(2:ℝ)^((d:ℝ)*b) :=
          mul_lt_mul_of_pos_right hpow hpos
    _ = (2:ℝ)^((d:ℝ)*(e:ℝ)) := by
      rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring

/-- The dominating binary power can be chosen in an even dimension above an
arbitrary dimension cutoff. -/
theorem exists_even_binary_power_growth (b : ℝ) (e : ℕ) (hbe : b<(e:ℝ))
    (C : ℝ) (N₀ d₀ : ℕ) :
    ∃ d : ℕ, Even d ∧ d₀≤d ∧ N₀≤2^d ∧
      C*(2:ℝ)^((d:ℝ)*b)<(2:ℝ)^((d:ℝ)*(e:ℝ)) := by
  let r : ℝ := (2:ℝ)^((e:ℝ)-b)
  have hr : 1<r := by
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr hbe)
  obtain ⟨d₁,hd₁⟩ := pow_unbounded_of_one_lt (N₀:ℝ) (by norm_num : (1:ℝ)<2)
  obtain ⟨d₂,hd₂⟩ := pow_unbounded_of_one_lt C hr
  let k := max (max d₁ d₂) d₀
  let d := 2*k
  have hd₁d : d₁≤d := by dsimp [d,k]; omega
  have hd₂d : d₂≤d := by dsimp [d,k]; omega
  have hd₀d : d₀≤d := by dsimp [d,k]; omega
  have hNreal : (N₀:ℝ)<(2:ℝ)^d := hd₁.trans_le (pow_le_pow_right₀ (by norm_num) hd₁d)
  have hN : N₀≤2^d := by exact_mod_cast hNreal.le
  have hCd : C<r^d := hd₂.trans_le (pow_le_pow_right₀ hr.le hd₂d)
  have hrform : r^d=(2:ℝ)^((d:ℝ)*((e:ℝ)-b)) := by
    rw [←Real.rpow_natCast]
    dsimp [r]
    rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hpow : C<(2:ℝ)^((d:ℝ)*((e:ℝ)-b)) := by rwa [←hrform]
  have hpos : 0<(2:ℝ)^((d:ℝ)*b) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨d,⟨k,by dsimp [d]; omega⟩,hd₀d,hN,?_⟩
  calc
    C*(2:ℝ)^((d:ℝ)*b)
        < (2:ℝ)^((d:ℝ)*((e:ℝ)-b))*(2:ℝ)^((d:ℝ)*b) :=
          mul_lt_mul_of_pos_right hpow hpos
    _ = (2:ℝ)^((d:ℝ)*(e:ℝ)) := by
      rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring

end BinaryFieldCounterexamples.Gold
