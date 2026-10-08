/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.AllRates.Parameters
/-!
# Uniform dimension cutoffs for dyadic padding

Exact power identities relate the seed size, witness dimension and graph count
to the full domain. A fixed cutoff absorbs rounding and reserves padding room
uniformly over all fields and domains of each larger binary dimension.
-/
@[expose] public section
namespace BinaryFieldCounterexamples

theorem all_rate_power_parameters (d ell s : ℕ) (hd : ell+s+2≤d) :
    let N : ℝ := 2^d
    let lam : ℝ := 1/2^ell
    let kap : ℝ := 1/2^(s+2)
    (2:ℝ)^(d-ell)=lam*N ∧
      (2:ℝ)^(d-ell-s-2)=lam*kap*N ∧
      (2:ℝ)^((d-ell-s)*s)=N^s/2^((ell+s)*s) := by
  dsimp only
  have h1 : (2:ℝ)^d=2^ell*2^(d-ell) := by
    rw [←pow_add,show ell+(d-ell)=d by omega]
  have h2 : (2:ℝ)^d=2^ell*2^(s+2)*2^(d-ell-s-2) := by
    rw [←pow_add,←pow_add,show ell+(s+2)+(d-ell-s-2)=d by omega]
  have h3 : (2:ℝ)^d=2^(ell+s)*2^(d-ell-s) := by
    rw [←pow_add,show ell+s+(d-ell-s)=d by omega]
  refine ⟨?_,?_,?_⟩
  · rw [h1]
    field_simp
  · rw [h2]
    field_simp
  · rw [h3,mul_pow,←pow_mul,←pow_mul]
    field_simp

theorem exists_all_rate_dimension_cutoff (ρ : ℝ) (hρ : 0<ρ) (hρ' : ρ<1)
    (ell s : ℕ)
    (hlow : 2*((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2))<ρ)
    (hroom : ρ<1-((1:ℝ)/2^ell)*(1-2*((1:ℝ)/2^(s+2)))) :
    ∃ d₀ : ℕ, ell+2*s+2≤d₀ ∧ ∀ d : ℕ, d₀≤d →
      let N : ℕ := 2^d
      let n : ℕ := 2^(d-ell)
      let K : ℕ := 2^(d-ell-s-2)
      let J : ℕ := ⌊ρ*N⌋₊
      2*K≤J ∧ J-2*K+1≤N-n ∧
        ⌈(ρ+((1:ℝ)/2^ell)*((1:ℝ)/2^(s+2)))*N⌉₊≤J+2*K ∧ J≤N := by
  let lam : ℝ := 1/2^ell
  let kap : ℝ := 1/2^(s+2)
  let gap : ℝ := 1-ρ-lam+2*lam*kap
  have hg : 0<gap := by dsimp [gap,lam,kap]; linarith
  obtain ⟨dg,hdg⟩ := pow_unbounded_of_one_lt (1/gap) (by norm_num : (1:ℝ)<2)
  refine ⟨max (ell+2*s+2) dg,le_max_left _ _,?_⟩
  intro d hd
  have hdd : ell+s+2≤d := by omega
  have hbound : 1/gap≤(2:ℝ)^d := hdg.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hgN : 1≤gap*(2:ℝ)^d := by
    have he := (div_le_iff₀ hg).mp hbound
    linarith
  obtain ⟨hn,hK,hM⟩ := all_rate_power_parameters d ell s hdd
  apply all_rate_padding_rounding ρ (lam*kap) (2^d) (2^(d-ell)) (2^(d-ell-s-2)) hρ.le hρ'.le
  · exact Nat.one_le_pow _ _ (by decide)
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,lam,kap] using hK
  · push_cast
    have hN : 0≤(2:ℝ)^d := by positivity
    have he := mul_le_mul_of_nonneg_right hlow.le hN
    linarith [hK]
  · push_cast
    dsimp [gap,lam,kap] at hgN
    linarith [hn,hK]

end BinaryFieldCounterexamples
