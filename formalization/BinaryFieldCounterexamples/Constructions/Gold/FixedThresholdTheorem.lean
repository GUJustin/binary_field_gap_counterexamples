/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.GoldCounting
public import BinaryFieldCounterexamples.Constructions.Gold.FiniteExtensions
public import BinaryFieldCounterexamples.Constructions.Gold.EnergyLowerBound
public import BinaryFieldCounterexamples.Constructions.Gold.FixedThresholdParameters
public import BinaryFieldCounterexamples.Constructions.Gold.FixedPowerGrowth
public import BinaryFieldCounterexamples.Constructions.Gold.FixedBudget
/-!
# The fixed-threshold Gold construction

This module assembles the finite Gold theorem in the fixed-parameter regime.
The extension exponent is fixed before the requested block-length cutoff.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq
set_option linter.style.haveILetI false

/-- The finite fixed-threshold construction with its extension exponent supplied
before the agreement threshold and count constant.  Every field, domain,
common-agreement and exceptional-challenge conclusion is the literal original one. -/
theorem no_fixed_polynomial_exceptional_bound_construction_of_exponent
    (e : ℕ) (a b C₀ : ℝ) (he2 : 2≤e) (hbe : b+1<(e:ℝ))
    (_ha : 1 / 4 < a) (ha' : a < 1 / 2)
    (hb : 0 < b) (_hC₀ : 0 < C₀) :
    ∀ N₀ : ℕ, ∃ d : ℕ, N₀ ≤ 2 ^ d ∧
    ∃ (B : Type) (fieldB : Field B) (finiteB : Fintype B),
    letI := fieldB
    letI := finiteB
    ∃ (_ : CharP B 2), Fintype.card B = 2 ^ (d + 1) ∧
    ∃ D : AddSubgroup B, (additiveDomain D).card = 2 ^ d ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F = (2 ^ (d + 1)) ^ e ∧
    let D' := mappedDomain φ (additiveDomain D)
    let N : ℕ := 2 ^ d
    ∃ f g : D' → F,
      commonAgreementEQ D' (N / 4) f g (N / 4) ∧
      C₀ * (N : ℝ) ^ b <
        (badChallenges D' (N / 4) f g ⌈a * N⌉₊).card := by
  obtain ⟨t,het,hat⟩ := Gold.exists_fixed_threshold_rank_of_exponent a e ha'
  have he1 : 1≤e := by omega
  have hbepred : b<((e-1:ℕ):ℝ) := by
    rw [Nat.cast_sub he1,Nat.cast_one]
    linarith
  intro N₀
  let d₀ := 2*(t*(t+1)+e+2)
  obtain ⟨d,heven,hd₀,hN₀,hgrowth⟩ :=
    Gold.exists_even_binary_power_growth b (e-1) hbepred (C₀+1) N₀ d₀
  have ht2 : 2≤t := he2.trans het
  have hdt : 2*t≤d := by
    apply le_trans _ hd₀
    dsimp [d₀]
    have htprod : t≤t*(t+1) := Nat.le_mul_of_pos_right t (by omega)
    omega
  have htd : t≤d/2 := by omega
  have hdpos : 0<d := by omega
  have hΔ : 1≤d+1-t*(d+1-d+if Even d then 1 else 0) := by
    rw [ite_eq_left heven]
    have : d+1-d=1 := by omega
    rw [this]
    dsimp [d₀] at hd₀
    omega
  have hexp : e*(d+1)≤d+(d-2*t)+2*(t*(d/2-t)) := by
    obtain ⟨r,hr⟩ := heven
    subst d
    have hmul : e*r≤t*r := Nat.mul_le_mul_right r het
    dsimp [d₀] at hd₀
    have hrbound : t*(t+1)+e+2≤r := by omega
    have hrhalf : (r+r)/2=r := by omega
    have hrsub : r+r-2*t=2*(r-t) := by omega
    have htr : t≤r := by omega
    have htrmul : t*(r-t)=t*r-t*t := by rw [Nat.mul_sub_left_distrib]
    rw [hrhalf,hrsub,htrmul]
    have htt : t*t≤t*r := Nat.mul_le_mul_left t htr
    have hmulZ : (e:ℤ)*(r:ℤ)≤(t:ℤ)*(r:ℤ) := by exact_mod_cast hmul
    have hrboundZ : (t:ℤ)*((t:ℤ)+1)+(e:ℤ)+2≤(r:ℤ) := by exact_mod_cast hrbound
    have hgoalZ : (e:ℤ)*((r:ℤ)+(r:ℤ)+1) ≤
        (r:ℤ)+(r:ℤ)+2*((r-t:ℕ):ℤ)+2*((t*r-t*t:ℕ):ℤ) := by
      rw [Nat.cast_sub htr,Nat.cast_sub htt]
      push_cast
      have heNonneg : (0:ℤ)≤e := by positivity
      linarith only [hmulZ, hrboundZ, heNonneg]
    exact_mod_cast hgoalZ
  obtain ⟨B,fieldB,finiteB,hBdata⟩ := Gold.exists_hyperplane_with_extension d e he1
  refine ⟨d,hN₀,B,fieldB,finiteB,?_⟩
  letI := fieldB
  letI := finiteB
  obtain ⟨charB,hB,D,hD,F,fieldF,finiteF,hFdata⟩ := hBdata
  refine ⟨charB,hB,D,hD,F,fieldF,finiteF,?_⟩
  letI := fieldF
  letI := finiteF
  obtain ⟨φ,hF⟩ := hFdata
  refine ⟨φ,hF,?_⟩
  letI : CharP F 2 := charP_of_injective_ringHom φ.injective 2
  let N : ℕ := 2^d
  let L : ℕ := 2^(2*t)*(2^(d+1-t*(d+1-d+if Even d then 1 else 0))-1)*
    gaussianBinomial 4 (d/2) t
  let T : ℕ := N/2-N/2^(t+1)
  let δ : ℕ := N/2^(2*t)
  let q : ℕ := Fintype.card F
  let Z : ℕ := ⌈(L:ℚ)*((q:ℚ)-(N:ℚ))/
    ((q:ℚ)-(N:ℚ)+(δ:ℚ)*((L:ℚ)-1))⌉₊-1
  have hq : q=(2^(d+1))^e := by exact hF
  have hNpos : 0<N := by dsimp [N]; positivity
  have hδpos : 0<δ := by
    dsimp [δ,N]
    rw [Nat.pow_div hdt (by decide)]
    positivity
  have h2Nq : 2*N≤q := by
    rw [hq]
    dsimp [N]
    rw [←pow_succ',←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.le_mul_of_pos_right (d+1) (by omega)
  have hqL : q≤δ*L := by
    rw [hq]
    dsimp [δ,L,N]
    rw [ite_eq_left heven]
    have hs : d+1-d=1 := by omega
    rw [hs]
    simpa only [one_add_one_eq_two,Nat.mul_comm t 2] using
      Gold.fixed_gold_field_le_collision_budget d e t hdt hexp
  have henergy := Gold.gold_energy_count_lower_bound N δ L q hNpos h2Nq hδpos hqL
  have hgold := gold_counting φ D 0 (d+1) d t hB hD ht2 htd hΔ (by
    dsimp [q,N] at h2Nq ⊢
    omega)
  have haffine : affineDomain (additiveDomain D) 0=additiveDomain D := by
    classical
    ext x
    simp [affineDomain]
  rw [haffine] at hgold
  dsimp only at hgold
  obtain ⟨f,g,hcommon,hg,hf,hbad,hbadstrong⟩ := hgold
  refine ⟨f,g,hcommon,?_⟩
  have hthreshold : ⌈a*(N:ℝ)⌉₊≤T := by
    apply Nat.ceil_le.mpr
    have hhalf : ((N/2:ℕ):ℝ)=(N:ℝ)/2 := by
      dsimp [N]
      rw [show 2^d/2=2^(d-1) by exact Nat.pow_div (x:=2) (m:=d) (n:=1) (by omega) (by decide)]
      rw [Nat.cast_pow,Nat.cast_pow]
      rw [show d=(d-1)+1 by omega,pow_succ]
      norm_num
    have hsmall : ((N/2^(t+1):ℕ):ℝ)=(N:ℝ)/(2:ℝ)^(t+1) := by
      dsimp [N]
      rw [Nat.pow_div (x:=2) (by omega : t+1≤d) (by decide)]
      rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
      apply (eq_div_iff (by positivity : (2:ℝ)^(t+1)≠0)).mpr
      rw [←pow_add,Nat.sub_add_cancel (by omega : t+1≤d)]
    have hsub : N/2^(t+1)≤N/2 := by
      dsimp [N]
      rw [Nat.pow_div (x:=2) (by omega : t+1≤d) (by decide),
        Nat.pow_div (x:=2) (by omega : 1≤d) (by decide)]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.cast_sub hsub,hhalf,hsmall]
    have hNreal : (0:ℝ)<N := by positivity
    exact (calc
      a*(N:ℝ) < (1/2-1/(2:ℝ)^(t+1))*(N:ℝ) := mul_lt_mul_of_pos_right hat hNreal
      _ = (N:ℝ)/2-(N:ℝ)/(2:ℝ)^(t+1) := by ring
      _ ≤ _ := le_rfl).le
  have hsubset : nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T ⊆
      badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g ⌈a*(N:ℝ)⌉₊ := by
    intro z hz
    have hz' : z∈badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T :=
      Finset.mem_of_mem_erase hz
    rw [mem_badChallenges] at hz' ⊢
    obtain ⟨p,hp,hagree⟩ := hz'
    exact ⟨p,hp,hthreshold.trans hagree⟩
  have hZcard : Z≤(badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g ⌈a*(N:ℝ)⌉₊).card :=
    hbad.trans (Finset.card_le_card hsubset)
  have hcountQ : (q:ℚ)/(4*δ)-1≤
      ((badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g ⌈a*(N:ℝ)⌉₊).card:ℚ) :=
    by
      change (q:ℚ)/(4*δ)-1≤(Z:ℚ) at henergy
      exact henergy.trans (by exact_mod_cast hZcard)
  have hgrowth' : C₀*(N:ℝ)^b+1<(N:ℝ)^(e-1:ℕ) := by
    have hNb : 1≤(N:ℝ)^b := by
      have hN1Nat : 1≤N := Nat.one_le_iff_ne_zero.mpr (by dsimp [N]; positivity)
      have hN1 : (1:ℝ)≤N := by exact_mod_cast hN1Nat
      exact Real.one_le_rpow hN1 hb.le
    have hform : (N:ℝ)^b=(2:ℝ)^((d:ℝ)*b) := by
      dsimp [N]
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,
        ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    have hforme : (N:ℝ)^(e-1:ℕ)=(2:ℝ)^((d:ℝ)*(e-1:ℕ)) := by
      calc
        (N:ℝ)^(e-1:ℕ) = (2:ℝ)^(d*(e-1)) := by
          dsimp [N]
          rw [Nat.cast_pow,Nat.cast_ofNat,←pow_mul]
        _ = (2:ℝ)^((d*(e-1):ℕ):ℝ) := (Real.rpow_natCast 2 (d*(e-1))).symm
        _ = (2:ℝ)^((d:ℝ)*(e-1:ℕ)) := by norm_cast
    rw [hform,hforme]
    calc
      C₀*(2:ℝ)^((d:ℝ)*b)+1 ≤ (C₀+1)*(2:ℝ)^((d:ℝ)*b) := by
        rw [hform] at hNb
        linarith only [hNb]
      _ < _ := hgrowth
  have hnatRatio : N^(e-1)*(4*δ)≤q := by
      rw [hq]
      dsimp [N,δ]
      rw [Nat.pow_div hdt (by decide),show 4=2^2 by norm_num,←pow_add,←pow_mul,←pow_add]
      rw [←pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      calc
        d*(e-1)+(2+(d-2*t)) ≤ d*(e-1)+d+2 := by omega
        _ = d*e+2 := by
          congr 1
          rw [Nat.mul_sub_left_distrib]
          simpa using Nat.sub_add_cancel (Nat.le_mul_of_pos_right d (by omega : 0<e))
        _ ≤ d*e+e := Nat.add_le_add_left he2 _
        _ = (d+1)*e := by ring
  have hratio : ((N ^ (e-1) : ℕ) : ℚ)≤(q:ℚ)/(4*δ) := by
    apply (le_div_iff₀ (by positivity : (0:ℚ)<4*δ)).mpr
    exact_mod_cast hnatRatio
  have hpowcardQ : ((N ^ (e-1) : ℕ) : ℚ)-1≤
      ((badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g ⌈a*(N:ℝ)⌉₊).card:ℚ) :=
    (sub_le_sub_right hratio 1).trans hcountQ
  have hpow1 : 1≤N^(e-1) := Nat.one_le_pow _ _ (by dsimp [N]; positivity)
  have hpowcard : N^(e-1)-1≤
      (badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g ⌈a*(N:ℝ)⌉₊).card := by
    exact_mod_cast hpowcardQ
  have hgrowthfinal : C₀*(N:ℝ)^b<((N^(e-1)-1:ℕ):ℝ) := by
    have hcastpow : (N:ℝ)^(e-1)=((N^(e-1):ℕ):ℝ) := by norm_cast
    rw [hcastpow] at hgrowth'
    rw [Nat.cast_sub hpow1,Nat.cast_one]
    linarith only [hgrowth']
  exact hgrowthfinal.trans_le (by exact_mod_cast hpowcard)


/-- The finite construction underlying the no-fixed-polynomial exceptional-set
bound. -/
theorem no_fixed_polynomial_exceptional_bound_construction
    (a b C₀ : ℝ) (_ha : 1 / 4 < a) (ha' : a < 1 / 2)
    (hb : 0 < b) (_hC₀ : 0 < C₀) :
    ∃ e : ℕ, ∀ N₀ : ℕ, ∃ d : ℕ, N₀ ≤ 2 ^ d ∧
    ∃ (B : Type) (fieldB : Field B) (finiteB : Fintype B),
    letI := fieldB
    letI := finiteB
    ∃ (_ : CharP B 2), Fintype.card B = 2 ^ (d + 1) ∧
    ∃ D : AddSubgroup B, (additiveDomain D).card = 2 ^ d ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F, Fintype.card F = (2 ^ (d + 1)) ^ e ∧
    let D' := mappedDomain φ (additiveDomain D)
    let N : ℕ := 2 ^ d
    ∃ f g : D' → F,
      commonAgreementEQ D' (N / 4) f g (N / 4) ∧
      C₀ * (N : ℝ) ^ b <
        (badChallenges D' (N / 4) f g ⌈a * N⌉₊).card := by
  obtain ⟨e,t,he2,hbe,het,hat⟩ := Gold.exists_fixed_threshold_parameters a b ha'
  refine ⟨e,?_⟩
  exact no_fixed_polynomial_exceptional_bound_construction_of_exponent
    e a b C₀ he2 hbe _ha ha' hb _hC₀

end BinaryFieldCounterexamples
