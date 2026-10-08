/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.Assembly
/-!
# A coarse lower bound for the Gold collision energy

For the fixed-threshold asymptotic regime, the exact collision quotient is
bounded below by a constant multiple of `q / δ`.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- If the challenge field has at least twice as many points as the domain and
does not exceed the total collision budget `δ L`, then the exact Gold energy
count is at least `q / (4 δ) - 1`. -/
theorem gold_energy_count_lower_bound (N δ L q : ℕ)
    (hN : 0<N) (h2N : 2*N≤q) (hδ : 0<δ) (hqL : q≤δ*L) :
    (q : ℚ)/(4*δ)-1 ≤
      ((⌈(L : ℚ)*((q : ℚ)-(N : ℚ)) /
        ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊-1 : ℕ) : ℚ) := by
  have hq : 0<q := by omega
  have hNq : N<q := by omega
  have hL : 1≤L := by
    by_contra h
    have : L=0 := by omega
    subst L
    simp at hqL
    omega
  let x : ℚ := (L : ℚ)*((q : ℚ)-(N : ℚ)) /
    ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))
  have hδQ : (0:ℚ)<δ := by exact_mod_cast hδ
  have hNqQ : (N:ℚ)<(q:ℚ) := by exact_mod_cast hNq
  have hqNQ : (0:ℚ)<(q:ℚ)-(N:ℚ) := by linarith
  have hLQ : (1:ℚ)≤(L:ℚ) := by exact_mod_cast hL
  have hLm1Q : (0:ℚ)≤(L:ℚ)-1 := by linarith
  have hdenpos : (0:ℚ)<(q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1) := by positivity
  have hhalf : (q:ℚ)/2 ≤ (q:ℚ)-(N:ℚ) := by
    have h2NQ : (2:ℚ)*(N:ℚ)≤(q:ℚ) := by exact_mod_cast h2N
    linarith
  have hqLQ : (q:ℚ)≤(δ:ℚ)*(L:ℚ) := by exact_mod_cast hqL
  have hdenle : (q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1) ≤
      2*(δ:ℚ)*(L:ℚ) := by
    linarith
  have hcross : (q:ℚ)*((q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1)) ≤
      (4*(δ:ℚ))*((L:ℚ)*((q:ℚ)-(N:ℚ))) := by
    have hqnonneg : (0:ℚ)≤q := by positivity
    have hδLnonneg : (0:ℚ)≤(δ:ℚ)*(L:ℚ) := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hdenle hqnonneg
    have h₂ := mul_le_mul_of_nonneg_right hhalf hδLnonneg
    linarith
  have hx : (q:ℚ)/(4*δ) ≤ x := by
    dsimp [x]
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<4*δ) hdenpos]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross
  have hxpos : (0:ℚ)<x := lt_of_lt_of_le (by positivity) hx
  have hceilpos : 0<⌈x⌉₊ := Nat.ceil_pos.mpr hxpos
  have hceil : x≤(⌈x⌉₊:ℚ) := Nat.le_ceil x
  rw [Nat.cast_sub (by omega : 1≤⌈x⌉₊), Nat.cast_one]
  exact sub_le_sub_right (hx.trans hceil) 1

/-- Under the same collision-budget hypothesis, once the challenge field has
at least `8δ` elements, the normalized exact Gold count is at least `1/(8δ)`. -/
theorem gold_energy_probability_lower_bound (N δ L q : ℕ)
    (hN : 0<N) (h2N : 2*N≤q) (hδ : 0<δ) (hqL : q≤δ*L)
    (h8δ : 8*δ≤q) :
    (1:ℚ)/(8*δ) ≤
      (⌈(L : ℚ)*((q : ℚ)-(N : ℚ)) /
        ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊-1 : ℕ)/(q:ℚ) := by
  let Z := ⌈(L : ℚ)*((q : ℚ)-(N : ℚ)) /
    ((q : ℚ)-(N : ℚ)+(δ : ℚ)*((L : ℚ)-1))⌉₊-1
  have hq : 0<q := by omega
  have hbase := gold_energy_count_lower_bound N δ L q hN h2N hδ hqL
  have hδQ : (0:ℚ)<δ := by exact_mod_cast hδ
  have hqQ : (0:ℚ)<q := by exact_mod_cast hq
  have h8δQ : (8:ℚ)*δ≤q := by exact_mod_cast h8δ
  have hhalf : (q:ℚ)/(8*δ)≤(q:ℚ)/(4*δ)-1 := by
    field_simp
    linarith
  have hZ : (q:ℚ)/(8*δ)≤(Z:ℚ) := hhalf.trans hbase
  apply (le_div_iff₀ hqQ).mpr
  dsimp only [Z] at hZ ⊢
  calc
    (1:ℚ)/(8*δ)*q = q/(8*δ) := by ring
    _ ≤ _ := hZ

end BinaryFieldCounterexamples.Gold
