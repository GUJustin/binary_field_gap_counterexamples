/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.Native128Example
public import BinaryFieldCounterexamples.Constructions.Gold.DenseAsymptoticTheorem
public import BinaryFieldCounterexamples.Constructions.Gold.RetentionLimit

/-!
# Dense half-rate Gold families

The consequently clause of Corollary 5.15 (p. 46) is assembled here
for the paper's actual padded received pair, rather than the quarter-rate pair.
The extension field is a rounded power of the base field. Exact retention loses
only a constant factor, so the quadratic logarithmic count exponent persists.
-/
@[expose] public section
namespace BinaryFieldCounterexamples.Gold
open Polynomial
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1200000

/-- The exact normalized half-rate deficit in Corollary 5.15 is three quarters
of the quarter-rate deficit, including the natural-number rounding conventions. -/
theorem halfRate_threshold_deficit_eq (d t : ℕ) (ht : 2 ≤ t) (hpad : 2*t ≤ d-2) :
    (5/8 : ℝ) - ((5*2^d/8-3*2^d/2^(t+3) : ℕ) : ℝ)/(2^d : ℕ) =
      (3/4 : ℝ) * (1/2 - ((2^d/2-2^d/2^(t+1) : ℕ) : ℝ)/(2^d : ℕ)) := by
  have he := halfRate_padding_count d t ht hpad
  have hd : 2 ≤ d := by omega
  have hsmall : 2^(d-2) ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
  have heR := congrArg (fun n : ℕ => (n : ℝ)) he
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub hsmall] at heR
  have hquarter : ((2^(d-2) : ℕ) : ℝ) * 4 = (2^d : ℕ) := by
    norm_cast
    rw [show 4 = (2:ℕ)^2 by norm_num, ←pow_add]
    congr 1
    omega
  have hN : (0 : ℝ) < (2^d : ℕ) := by positivity
  have hlin : 4 * ((5*2^d/8-3*2^d/2^(t+3) : ℕ) : ℝ) =
      (2^d : ℕ) + 3*((2^d/2-2^d/2^(t+1) : ℕ) : ℝ) := by
    nlinarith [congrArg (fun x : ℝ => x * ((2^d : ℕ) : ℝ)) hquarter,
      congrArg (fun x : ℝ => x * ((2^d/2-2^d/2^(t+1) : ℕ) : ℝ)) hquarter]
  field_simp
  linarith [hlin]

/-- Corollary 5.15's padded pair in the dense finite regime has exceptional
probability at least `1/(32δ)` in the same rounded extension field. -/
theorem denseGold_halfRate_finite
    {B : Type} [Field B] [Fintype B] [CharP B 2]
    (D : AddSubgroup B) (a : B) (c d t : ℕ)
    (hB : Fintype.card B=2^(d+c)) (hD : (additiveDomain D).card=2^d)
    (ht2 : 2≤t) (htd : t≤d/2) (hpad : 2*t≤d-2)
    (hΔ : 1≤d+c-t*(c+if Even d then 1 else 0))
    (hell : d+c≤denseGoldExponent c d t)
    (hqexp : d+1≤denseGoldExponent c d t-(d+c))
    (h8exp : 3+(d-2*t)≤(d+c)*denseGoldExtensionDegree c d t) :
    let N : ℕ := 2^d
    let δ : ℕ := N/2^(2*t)
    let T : ℕ := 5*N/8-3*N/2^(t+3)
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
    letI := fieldF
    letI := finiteF
    ∃ φ : B →+* F,
      Fintype.card F=(2^(d+c))^(denseGoldExtensionDegree c d t) ∧
      let D' := mappedDomain φ (affineDomain (additiveDomain D) a)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N/2) f g (N/2) ∧
        (Fintype.card F : ℚ)/(32*δ) ≤
          (nonzeroBadChallenges D' (N/2) f g T).card := by
  classical
  dsimp only
  obtain ⟨_, F, fieldF, finiteF, hrest⟩ :=
    denseGold_finite D c d t hB hD ht2 htd hΔ hell hqexp h8exp
  refine ⟨F,fieldF,finiteF,?_⟩
  letI := fieldF
  letI := finiteF
  obtain ⟨φ,hq,_⟩ := hrest
  letI : CharP F 2 := charP_of_injective_ringHom φ.injective 2
  refine ⟨φ,hq,?_⟩
  let N : ℕ := 2^d
  let δ : ℕ := N/2^(2*t)
  let L : ℕ := 2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
    gaussianBinomial 4 (d/2) t
  let q : ℕ := Fintype.card F
  let Z : ℕ := ⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+δ*((L:ℚ)-1))⌉₊-1
  have hdt : 2*t≤d := by omega
  have hδ : δ=2^(d-2*t) := Nat.pow_div hdt (by decide)
  have hqpow : q=2^((d+c)*denseGoldExtensionDegree c d t) := by
    dsimp [q]
    rw [hq,←pow_mul]
  have hm : 0<d+c := by omega
  have hround := denseGold_rounding_lower c d t hm hell
  have hqexp' : d+1≤(d+c)*denseGoldExtensionDegree c d t := hqexp.trans hround.le
  have h2N : 2*N≤q := by
    rw [hqpow]
    dsimp [N]
    rw [←pow_succ']
    exact Nat.pow_le_pow_right (by decide) hqexp'
  have hNq : 2^d<q := by
    dsimp [N] at h2N
    have hNpos : 0<(2:ℕ)^d := by positivity
    omega
  have h8δ : 8*δ≤q := by
    rw [hqpow,hδ,show 8=2^3 by norm_num,←pow_add]
    exact Nat.pow_le_pow_right (by decide) h8exp
  have hL : q≤L := by
    dsimp [q,L]
    rw [hq]
    exact denseGold_extension_card_le_list c d t htd hΔ
  have hδpos : 0<δ := by rw [hδ]; positivity
  have hqL : q≤δ*L := hL.trans (Nat.le_mul_of_pos_left L hδpos)
  have hΔ' : 1≤d+c-t*(d+c-d+if Even d then 1 else 0) := by
    simpa only [show d+c-d=c by omega] using hΔ
  have hhalf := gold_half_rate_sharp φ D a (d+c) d t
    hB hD ht2 htd hpad hΔ' hNq
  dsimp only at hhalf
  rw [show d+c-d=c by omega] at hhalf
  obtain ⟨f,g,hcommon,hbad⟩ := hhalf
  refine ⟨f,g,hcommon,?_⟩
  have henergy := gold_energy_probability_lower_bound N δ L q
    (by dsimp [N]; positivity) h2N hδpos hqL h8δ
  have hqpos : (0:ℚ)<q := by dsimp [q]; positivity
  have hZ : (q:ℚ)/(8*δ) ≤ (Z:ℚ) := by
    have he := (le_div_iff₀ hqpos).mp henergy
    simpa [Z,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using he
  have hp := (paddingRetentionProbability_gt_quarter d (d-2) (2*t) hpad (by omega)).le
  have hmul := mul_le_mul_of_nonneg_right hp (show (0:ℚ)≤Z by positivity)
  have hceil := Nat.le_ceil (paddingRetentionProbability d (d-2) (2*t) *
    (max (L-(δ*L.choose 2)/(q-N))
      ⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+δ*((L:ℚ)-1))⌉₊ : ℕ))
  have hbadQ : (⌈paddingRetentionProbability d (d-2) (2*t)*
    (max (L-(δ*L.choose 2)/(q-N))
      ⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+δ*((L:ℚ)-1))⌉₊ : ℕ)⌉₊ : ℚ) ≤
      (nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a)) (N/2) f g
        (5*N/8-3*N/2^(t+3))).card := by
    apply Nat.cast_le.mpr
    simpa only [L,N,δ,q] using hbad
  have hZmax : Z ≤ max (L-(δ*L.choose 2)/(q-N))
      ⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+δ*((L:ℚ)-1))⌉₊ :=
    (Nat.sub_le _ _).trans (le_max_right _ _)
  have hmulmax := mul_le_mul_of_nonneg_left (show (Z:ℚ)≤
    (max (L-(δ*L.choose 2)/(q-N))
      ⌈(L:ℚ)*((q:ℚ)-N)/((q:ℚ)-N+δ*((L:ℚ)-1))⌉₊ : ℕ) by exact_mod_cast hZmax)
    (le_trans (by norm_num : (0:ℚ)≤1/4) hp)
  have : (q:ℚ)/(32*δ) ≤ (1/4:ℚ)*(Z:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hZ (by norm_num : (0:ℚ)≤1/4)
    convert hh using 1 <;> ring
  exact this.trans (hmul.trans (hmulmax.trans (hceil.trans hbadQ)))

/-- The consequently clause of Corollary 5.15: every sufficiently large dense
binary domain supports a half-rate pair with quasipolynomially many distinct
nonzero exceptional challenges. Agreement is `5/8 - Θ(N^(-θ))`, hence its gap
above the exact common agreement `1/2` is `1/8 - Θ(N^(-θ))`. Constants depend
only on the fixed codimension `c`, including two-sided challenge-field bounds. -/
theorem denseGold_halfRate_asymptotic (c : ℕ) :
    let θ : ℝ := min (1 / 4) (1 / (c + 1))
    ∃ A C p : ℝ, 0 < A ∧ 0 < C ∧ 0 < p ∧ ∃ d₀ : ℕ,
    ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2 ^ (d + c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2 ^ d →
    ∀ a : B,
    let N : ℕ := 2 ^ d
    let E : ℝ := θ * (1 - 2 * θ) * (d : ℝ) ^ 2
    ∃ T : ℕ,
      A * (N : ℝ) ^ (-θ) ≤ 5 / 8 - (T : ℝ) / N ∧
      5 / 8 - (T : ℝ) / N ≤ C * (N : ℝ) ^ (-θ) ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (affineDomain (additiveDomain D) a)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N / 2) f g (N / 2) ∧
        (2 : ℝ) ^ (E - C * d) ≤
          (nonzeroBadChallenges D' (N / 2) f g T).card ∧
        p * (N : ℝ) ^ (-1 + 2 * θ) ≤
          ((nonzeroBadChallenges D' (N / 2) f g T).card : ℝ) / Fintype.card F ∧
        (2 : ℝ) ^ (E - C * d) ≤ Fintype.card F ∧
        (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ (E + C * d) := by
  dsimp only
  let A : ℝ := 3 / 16
  let C : ℝ := 32 * (c + 1)
  let p : ℝ := 1 / 512
  obtain ⟨d₀, hparams⟩ := exists_denseParameter_bundle c
  refine ⟨A, C, p, by norm_num [A], by positivity, by norm_num [p], d₀, ?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD a
  let t := denseT c d
  let N := 2 ^ d
  let L := 2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
    gaussianBinomial 4 (d/2) t
  let T := 5*N/8-3*N/2^(t+3)
  let δ := N/2^(2*t)
  let E : ℝ := denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ)^2
  have hp := hparams d hd
  dsimp only at hp
  obtain ⟨hguard, ht2, htd, hDelta, hell, hqexp, h8exp, hlistpow,
    hfieldlow, hfieldhigh⟩ := hp
  obtain ⟨hdeflow, hdefhigh⟩ := denseThreshold_deficit_bounds c d hguard
  have hquarter := denseT_le_quarter c d
  have hpad : 2*t ≤ d-2 := by dsimp [t]; omega
  have hdefeq := halfRate_threshold_deficit_eq d t ht2 hpad
  have hfinite := denseGold_halfRate_finite D a c d t hB hD ht2 htd hpad hDelta hell hqexp h8exp
  dsimp only at hfinite
  obtain ⟨F, fieldF, finiteF, hrest⟩ := hfinite
  refine ⟨T, ?_, ?_, F, fieldF, finiteF, ?_⟩
  · have hlo : (1/4:ℝ)*(N:ℝ)^(-denseTheta c) ≤
        1/2 - ((N/2-N/2^(t+1):ℕ):ℝ)/N := by
      simpa [N,t] using hdeflow
    have heq : (5/8:ℝ)-(T:ℝ)/N =
        (3/4:ℝ)*(1/2-((N/2-N/2^(t+1):ℕ):ℝ)/N) := by
      simpa [T,N] using hdefeq
    change A*(N:ℝ)^(-denseTheta c) ≤ 5/8-(T:ℝ)/N
    rw [heq]
    dsimp [A]
    linarith [hlo]
  · have hhi : 1/2 - ((N/2-N/2^(t+1):ℕ):ℝ)/N ≤
        2*(N:ℝ)^(-denseTheta c) := by
      simpa [N,t] using hdefhigh
    have heq : (5/8:ℝ)-(T:ℝ)/N =
        (3/4:ℝ)*(1/2-((N/2-N/2^(t+1):ℕ):ℝ)/N) := by
      simpa [T,N] using hdefeq
    have hC : (3/2:ℝ)≤C := by
      dsimp [C]
      nlinarith [show (0:ℝ)≤c by positivity]
    change 5/8-(T:ℝ)/N ≤ C*(N:ℝ)^(-denseTheta c)
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hC
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤(N:ℝ)) (-denseTheta c))
    linarith [hhi]
  · letI := fieldF
    letI := finiteF
    obtain ⟨φ, hq, f, g, hcommon, hcountQ⟩ := hrest
    refine ⟨φ, f, g, hcommon, ?_, ?_, ?_, ?_⟩
    · have hdt : 2 * t ≤ d := by
        have htd' : t ≤ d / 2 := htd
        omega
      have hδ : δ = 2 ^ (d - 2 * t) := by
        dsimp [δ, N]
        exact Nat.pow_div hdt (by decide)
      have hrL := (denseRoundedExponent_bounds c d hguard).1
      have hguardR : (16 : ℝ) * (c + 1) ≤ d := by exact_mod_cast hguard
      have hdR : (1 : ℝ) ≤ d := by
        have hcR : (0 : ℝ) ≤ c := by positivity
        linarith only [hguardR, hcR]
      have hexp : E - C * d + ((5 + (d - 2 * t) : ℕ) : ℝ) ≤
          (((d + c) * denseGoldExtensionDegree c d t : ℕ) : ℝ) := by
        have hrL' : E - 10 * ((c + 1 : ℕ) : ℝ) * d ≤
            (((d + c) * denseGoldExtensionDegree c d t : ℕ) : ℝ) := by
          simpa [E, t, denseR] using hrL
        have hsubR : ((d - 2 * t : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d (2*t)
        norm_num only [Nat.cast_add, Nat.cast_one] at hrL' hsubR ⊢
        dsimp [C]
        push_cast at hguardR hrL' hsubR ⊢
        have hcR : (0 : ℝ) ≤ c := by positivity
        nlinarith only [hrL', hsubR, hdR, hcR]
      have hscale : (32 : ℝ) * (δ : ℝ) =
          (2 : ℝ) ^ (((5 + (d - 2 * t) : ℕ) : ℝ)) := by
        rw [hδ, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      have hmul : (2 : ℝ) ^ (E - C * d) * ((32 : ℝ) * δ) ≤
          Fintype.card F := by
        rw [hscale, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hqR]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hden : (0 : ℝ) < 32 * δ := by positivity
      have hxratio : (2 : ℝ) ^ (E - C * d) ≤
          (Fintype.card F : ℝ) / (32 * δ) := (le_div_iff₀ hden).2 hmul
      have hcountR : (Fintype.card F : ℝ) / (32 * δ) ≤
          (nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a)) (N/2) f g T).card := by
        have hc := (Rat.cast_le (K := ℝ)).2 hcountQ
        norm_num [Rat.cast_div] at hc
        simpa [N,T,δ] using hc
      exact hxratio.trans hcountR
    · have hdt : 2 * t ≤ d := by
        have htd' : t ≤ d / 2 := htd
        omega
      have hδ : δ = 2 ^ (d - 2 * t) := by
        dsimp [δ, N]
        exact Nat.pow_div hdt (by decide)
      obtain ⟨htL, htU⟩ := denseT_real_bounds c d (by omega)
      have hexp : (-9 : ℝ) + (d : ℝ) * (-1 + 2 * denseTheta c) ≤
          -((5 + (d - 2 * t) : ℕ) : ℝ) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hsubR : ((d - 2*t : ℕ) : ℝ) = (d : ℝ) - 2*t := by
          rw [Nat.cast_sub hdt]
          push_cast
          rfl
        rw [hsubR]
        change denseTheta c * (d : ℝ) - 2 ≤ (t : ℝ) at htL
        linarith only [htL]
      have hNpow : (N : ℝ) ^ (-1 + 2 * denseTheta c) =
          (2 : ℝ) ^ ((d : ℝ) * (-1 + 2 * denseTheta c)) := by
        dsimp [N]
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hpform : p = (2 : ℝ) ^ (-9 : ℝ) := by
        dsimp [p]
        norm_num [Real.rpow_neg]
      have hinv : (1 : ℝ) / (32 * δ) =
          (2 : ℝ) ^ (-((5 + (d - 2*t) : ℕ) : ℝ)) := by
        rw [hδ, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (32 : ℝ) = (2 : ℝ)^5 by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have htarget : p * (N : ℝ) ^ (-1 + 2 * denseTheta c) ≤
          (1 : ℝ) / (32 * δ) := by
        rw [hpform, hNpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hinv]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have hprobR : (1 : ℝ) / (32 * δ) ≤
          ((nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a)) (N/2) f g T).card : ℝ) /
            Fintype.card F := by
        have hc := (Rat.cast_le (K := ℝ)).2 hcountQ
        norm_num [Rat.cast_div] at hc
        have hcountR : (Fintype.card F:ℝ)/(32*δ) ≤
            (nonzeroBadChallenges (mappedDomain φ (affineDomain (additiveDomain D) a)) (N/2) f g T).card := by
          simpa [N,T,δ] using hc
        apply (le_div_iff₀ (by positivity : (0:ℝ)<Fintype.card F)).mpr
        convert hcountR using 1 <;> ring
      simpa [N, denseTheta] using htarget.trans hprobR
    · have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      rw [hqR]
      have hlow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (show E-C*d ≤ E-16*((c+1:ℕ):ℝ)*d by
          dsimp [C]
          push_cast
          have hcd : (0:ℝ)≤((c:ℝ)+1)*d := by positivity
          nlinarith only [hcd])
      exact hlow.trans (by simpa [E,t,denseTheta] using hfieldlow)
    · have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      rw [hqR]
      have hhigh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (show E+16*((c+1:ℕ):ℝ)*d ≤ E+C*d by
          dsimp [C]
          push_cast
          have hcd : (0:ℝ)≤((c:ℝ)+1)*d := by positivity
          nlinarith only [hcd])
      exact (show (2:ℝ)^((((d+c)*denseGoldExtensionDegree c d t:ℕ):ℝ)) ≤
        (2:ℝ)^(E+16*((c+1:ℕ):ℝ)*d) by
          simpa [E,t,denseTheta] using hfieldhigh).trans hhigh


end BinaryFieldCounterexamples.Gold
