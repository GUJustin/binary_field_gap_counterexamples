/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Counting.CollisionAveraging
/-!
# Exact saturation of the collision-pooling bound

Once the actual family exceeds the square of one less than the field size, the
integer second-moment bound reaches every field element. Zero is retained in
this saturation step.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

theorem collision_pooling_ceil_eq_field_size (q M : ℕ) (hq : 0<q) (hM : (q-1)^2<M) :
    ⌈(q:ℚ)*M/(q+M-1)⌉₊=q := by
  have hqR : (1:ℚ)≤q := by exact_mod_cast hq
  have hMR : ((q:ℚ)-1)^2<M := by
    have he : ((q-1:ℕ):ℚ)=(q:ℚ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [←he]
    exact_mod_cast hM
  have hmR : (0:ℚ)<M := by linarith [sq_nonneg ((q:ℚ)-1)]
  have hden : (0:ℚ)<q+M-1 := by linarith
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · have hlt : q-1<⌈(q:ℚ)*M/(q+M-1)⌉₊ := by
      apply Nat.lt_ceil.mpr
      rw [Nat.cast_sub (by omega : 1≤q)]
      norm_num only [Nat.cast_one]
      apply (lt_div_iff₀ hden).mpr
      linarith
    omega
end BinaryFieldCounterexamples
