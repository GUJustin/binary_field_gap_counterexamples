/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.PaperSemantics
/-!
# Rate parameters and rounding margins

A sufficiently small fixed dyadic seed fraction places the target agreement
strictly between the rate and its Johnson threshold while reserving enough
coordinates for padding. The finite rounding lemma keeps natural floors and
ceilings, including the single extra padding point introduced by division by X.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

theorem exists_all_rate_dyadic_fraction (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1) (s : ℕ) :
    ∃ ell : ℕ,
      let lam : ℝ := 1/2^ell
      let kap : ℝ := 1/2^(s+2)
      0<lam ∧ 2*lam*kap<ρ ∧ ρ<1-lam*(1-2*kap) ∧
        ρ<ρ+lam*kap ∧ ρ+lam*kap<Real.sqrt ρ := by
  have hgap : ρ<Real.sqrt ρ := by
    nlinarith [Real.sq_sqrt hρ.le,Real.sqrt_nonneg ρ,mul_pos hρ (sub_pos.mpr hρ')]
  let eps := min (ρ/2) (min (1-ρ) (Real.sqrt ρ-ρ))
  have heps : 0<eps := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  obtain ⟨ell,hell⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1/2:ℝ)<1)
  have hl : (1:ℝ)/2^ell<eps := by simpa only [one_div_pow] using hell
  have hl0 : 0<(1:ℝ)/2^ell := by positivity
  have hk0 : 0<(1:ℝ)/2^(s+2) := by positivity
  have hk1 : (1:ℝ)/2^(s+2)≤1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have h1 := hl.trans_le (min_le_left _ _)
  have h2 := hl.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h3 := hl.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ell,hl0,?_,?_,?_,?_⟩
  · linarith [mul_le_mul_of_nonneg_left hk1 hl0.le]
  · linarith [mul_pos hl0 hk0]
  · linarith [mul_pos hl0 hk0]
  · linarith [mul_le_mul_of_nonneg_left hk1 hl0.le]
theorem all_rate_padding_rounding (ρ δ : ℝ) (N n K : ℕ)
    (hρ : 0≤ρ) (hρ' : ρ≤1) (hK : 1≤K)
    (hδ : (K:ℝ)=δ*N) (hlow : 2*(K:ℝ)≤ρ*N)
    (hroom : ρ*N+n+1≤N+2*(K:ℝ)) :
    let J : ℕ := ⌊ρ*N⌋₊
    2*K≤J ∧ J-2*K+1≤N-n ∧ ⌈(ρ+δ)*N⌉₊≤J+2*K ∧ J≤N := by
  let J : ℕ := ⌊ρ*N⌋₊
  have hfl : (J:ℝ)≤ρ*N := Nat.floor_le (mul_nonneg hρ (Nat.cast_nonneg N))
  have hlo : 2*K≤J := (Nat.le_floor_iff (mul_nonneg hρ (Nat.cast_nonneg N))).mpr (by exact_mod_cast hlow)
  have hroom' : J+n+1≤N+2*K := by
    exact_mod_cast (show (J:ℝ)+n+1≤N+2*(K:ℝ) by linarith)
  have hlt : ρ*N<(J:ℝ)+1 := Nat.lt_floor_add_one _
  have hceil : ⌈(ρ+δ)*N⌉₊≤J+2*K := by
    apply Nat.ceil_le.mpr
    push_cast
    have hKr : (1:ℝ)≤K := by exact_mod_cast hK
    linarith
  have hJN : J≤N := by
    exact_mod_cast hfl.trans (show ρ*(N:ℝ)≤N by nlinarith [show (0:ℝ)≤N from Nat.cast_nonneg N])
  exact ⟨hlo,by omega,hceil,hJN⟩
end BinaryFieldCounterexamples
