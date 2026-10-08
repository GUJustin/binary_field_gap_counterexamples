/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.Gold.FixedExtensionFinite
public import BinaryFieldCounterexamples.Constructions.Gold.FiniteExtensions
public import BinaryFieldCounterexamples.Constructions.Gold.FixedThresholdParameters
public import BinaryFieldCounterexamples.Constructions.Gold.FixedPowerGrowth
/-!
# Fixed thresholds with a supplied extension exponent greater than the count exponent

The fixed-extension constant-probability construction yields order `N^e`
distinct challenges. Thus every prescribed `e≥2` with `b<e` suffices,
while the threshold and multiplicative constant are chosen later. This does
not change the earlier fixed-rank endpoint or assert the sharp probability
coefficient of Corollary 5.3.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq
set_option linter.style.haveILetI false

/-- A supplied exponent `e≥2` greater than `b` supports arbitrarily large
fixed-threshold counterexamples, uniformly before the threshold and constant. -/
theorem optimal_fixed_threshold_of_exponent
    (e : ℕ) (b : ℝ) (he : 2≤e) (hb : 0<b) (hbe : b<(e:ℝ)) :
    ∀ (a C₀ : ℝ), 1/4<a → a<1/2 → 0<C₀ →
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
  intro a C₀ _ha ha' hC₀ N₀
  obtain ⟨t,het,hat⟩ := Gold.exists_fixed_threshold_rank_of_exponent a e ha'
  let n₀ := max (e+t) (2*e^2)
  let c : ℝ := 8*(2:ℝ)^(2*e-1)
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨d,hdEven,hcut,hNcut,hgrowth⟩ :=
    Gold.exists_even_binary_power_growth b e hbe (C₀*c) (2*N₀) (2*n₀)
  obtain ⟨n,rfl⟩ := hdEven
  rw [show n+n=2*n by omega] at hcut hNcut hgrowth
  have hn₀ : n₀≤n := by omega
  have hnt : e+t≤n := (Nat.le_max_left _ _).trans hn₀
  have hlarge : 2*e^2≤n := (Nat.le_max_right _ _).trans hn₀
  have hn : e+2≤n := by omega
  let N : ℕ := 2^(2*n-1)
  have hN2 : 2*N=2^(2*n) := by
    dsimp [N]
    rw [←pow_succ']
    congr 1
    omega
  have hN₀ : N₀≤N := by rw [←hN2] at hNcut; omega
  obtain ⟨B,fieldB,finiteB,hBdata⟩ :=
    Gold.exists_hyperplane_with_extension (2*n-1) e (by omega)
  refine ⟨2*n-1,hN₀,B,fieldB,finiteB,?_⟩
  letI := fieldB
  letI := finiteB
  obtain ⟨charB,hB,D,hD,F,fieldF,finiteF,hFdata⟩ := hBdata
  refine ⟨charB,hB,D,hD,F,fieldF,finiteF,?_⟩
  letI := fieldF
  letI := finiteF
  obtain ⟨φ,hF⟩ := hFdata
  refine ⟨φ,hF,?_⟩
  letI : CharP F 2 := charP_of_injective_ringHom φ.injective 2
  have hB' : Fintype.card B=2^(2*n) := by
    simpa only [show 2*n-1+1=2*n by omega] using hB
  have hF' : Fintype.card F=(2^(2*n))^e := by
    simpa only [show 2*n-1+1=2*n by omega] using hF
  have hpair := Gold.gold_fixed_extension_constant_probability φ D 0 n e he hn hlarge hB' hD hF'
  have haffine : affineDomain (additiveDomain D) 0=additiveDomain D := by
    ext x
    simp [affineDomain]
  rw [haffine] at hpair
  obtain ⟨f,g,hcommon,_hg,_hf,hcount⟩ := hpair
  dsimp only
  refine ⟨f,g,hcommon,?_⟩

  -- The growing rank raises the agreement threshold above the fixed request.
  have hat' : a<1/2-1/(2:ℝ)^(n-e+1) := by
    have hp : (2:ℝ)^(t+1)≤(2:ℝ)^(n-e+1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(2:ℝ)^(t+1)) hp
    linarith
  have hthreshold : ⌈a*(N:ℝ)⌉₊≤2^(2*n-2)-2^(n+e-2) := by
    rw [←Gold.fixed_extension_threshold_eq n e he hn]
    apply Nat.ceil_le.mpr
    have hhalf : ((N/2:ℕ):ℝ)=(N:ℝ)/2 := by
      have hnat : 2*(N/2)=N := by
        dsimp [N]
        have hh := Nat.pow_div (x:=2) (m:=2*n-1) (n:=1) (by omega) (by decide)
        simp only [pow_one] at hh
        rw [hh,←pow_succ']
        congr 1
        omega
      have hh : (2:ℝ)*(N/2:ℕ)=N := by exact_mod_cast hnat
      linarith
    have hsmall : ((N/2^(n-e+1):ℕ):ℝ)=(N:ℝ)/(2:ℝ)^(n-e+1) := by
      dsimp [N]
      rw [Nat.pow_div (by omega : n-e+1≤2*n-1) (by decide)]
      rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
      apply (eq_div_iff (by positivity : (2:ℝ)^(n-e+1)≠0)).mpr
      rw [←pow_add,Nat.sub_add_cancel (by omega : n-e+1≤2*n-1)]
    have hsub : N/2^(n-e+1)≤N/2 := by
      dsimp [N]
      have hh := Nat.pow_div (x:=2) (m:=2*n-1) (n:=1) (by omega) (by decide)
      simp only [pow_one] at hh
      rw [Nat.pow_div (by omega : n-e+1≤2*n-1) (by decide),hh]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    change a*(N:ℝ)≤((N/2-N/2^(n-e+1):ℕ):ℝ)
    rw [Nat.cast_sub hsub,hhalf,hsmall]
    have hNpos : (0:ℝ)<N := by dsimp [N]; positivity
    exact (calc
      a*(N:ℝ)<(1/2-1/(2:ℝ)^(n-e+1))*(N:ℝ) := mul_lt_mul_of_pos_right hat' hNpos
      _ = (N:ℝ)/2-(N:ℝ)/(2:ℝ)^(n-e+1) := by ring).le
  have hsubset : nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g
      (2^(2*n-2)-2^(n+e-2)) ⊆
      badChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g ⌈a*(N:ℝ)⌉₊ := by
    intro z hz
    have hz' := Finset.mem_of_mem_erase hz
    rw [mem_badChallenges] at hz' ⊢
    obtain ⟨p,hp,hag⟩ := hz'
    exact ⟨p,hp,hthreshold.trans hag⟩
  have hcountR : (Fintype.card F:ℝ)/c≤
      ((nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g
        (2^(2*n-2)-2^(n+e-2))).card:ℝ) := by
    have hh : (((Fintype.card F:ℚ)/(8*(2:ℚ)^(2*e-1)):ℚ):ℝ) ≤
        (((nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g
          (2^(2*n-2)-2^(n+e-2))).card:ℚ):ℝ) := by
      exact Rat.cast_le.mpr hcount
    push_cast at hh
    exact hh

  -- Constant probability has the full field exponent, so only `b<e` is needed.
  have hqR : (Fintype.card F:ℝ)=(2:ℝ)^(((2*n:ℕ):ℝ)*(e:ℝ)) := by
    rw [hF',Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,←pow_mul,←Real.rpow_natCast]
    norm_cast
  have hNBig : (N:ℝ)≤(2:ℝ)^(2*n) := by
    exact_mod_cast (show N≤2^(2*n) by rw [←hN2]; omega)
  have hpow : (N:ℝ)^b≤(2:ℝ)^(((2*n:ℕ):ℝ)*b) := by
    have hh := Real.rpow_le_rpow (by positivity : (0:ℝ)≤N) hNBig hb.le
    have hform : ((2:ℝ)^(2*n))^b=(2:ℝ)^(((2*n:ℕ):ℝ)*b) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rwa [hform] at hh
  have hstrict : C₀*(N:ℝ)^b<(Fintype.card F:ℝ)/c := by
    apply (lt_div_iff₀ hc).mpr
    rw [hqR]
    have hm := mul_le_mul_of_nonneg_left hpow (show 0≤C₀*c by positivity)
    have hlt := hm.trans_lt hgrowth
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hlt
  exact hstrict.trans_le (hcountR.trans (by exact_mod_cast Finset.card_le_card hsubset))

end BinaryFieldCounterexamples
