/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.LargerExtension
public import BinaryFieldCounterexamples.Constructions.Gold.DenseAsymptoticTheorem

/-!
# Main theorem companion: Corollary 5.2 in every larger extension

The quasipolynomial challenge-field choice and all original asymptotic clauses
are retained. Every field containing the original base field and at least
as large as that chosen field supplies a pair with the same superpolynomial
count. It need not contain the chosen challenge field.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Gold
attribute [local instance] Classical.decEq Classical.propDecidable
set_option maxHeartbeats 1200000

/-- Corollary 5.2 and Section 1's larger-extension clause, assembled with the
original two-sided deficit, decoding list, count, probability and chosen-field
bounds. Every at-least-as-large containing field has the same count guarantee. -/
theorem superpolynomial_near_johnson_every_larger_extension (c : ℕ) :
    let θ : ℝ := min (1 / 4) (1 / (c + 1))
    ∃ A C p : ℝ, 0 < A ∧ 0 < C ∧ 0 < p ∧ ∃ d₀ : ℕ,
    ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2 ^ (d + c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2 ^ d →
    let N : ℕ := 2 ^ d
    let E : ℝ := θ * (1 - 2 * θ) * (d : ℝ) ^ 2
    ∃ T L : ℕ,
      A * (N : ℝ) ^ (-θ) ≤ 1 / 2 - (T : ℝ) / N ∧
      1 / 2 - (T : ℝ) / N ≤ C * (N : ℝ) ^ (-θ) ∧
      (2 : ℝ) ^ (E - C * d) ≤ L ∧
      ordinaryList (additiveDomain D) (N / 4) T L ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      let := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (additiveDomain D)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N / 4) f g (N / 4) ∧
        (2 : ℝ) ^ (E - C * d) ≤
          (nonzeroBadChallenges D' (N / 4) f g T).card ∧
        p * (N : ℝ) ^ (-1 + 2 * θ) ≤
          ((nonzeroBadChallenges D' (N / 4) f g T).card : ℝ) / Fintype.card F ∧
        (2 : ℝ) ^ (E - C * d) ≤ Fintype.card F ∧
        (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ (E + C * d) ∧
        ∀ (G : Type) [Field G] [Fintype G] [CharP G 2]
          (ψ : B →+* G), Fintype.card F ≤ Fintype.card G →
          let D'' := mappedDomain ψ (additiveDomain D)
          ∃ u v : D'' → G,
            commonAgreementEQ D'' (N / 4) u v (N / 4) ∧
            agreementEQ D'' (N / 4) v (N / 4) ∧
            agreementLE D'' (N / 4) u (3 * N / 8 - 1) ∧
            (2 : ℝ) ^ (E - C * d) ≤
              (nonzeroBadChallenges D'' (N / 4) u v T).card := by
  dsimp only
  let A : ℝ := 1 / 4
  let C : ℝ := 16 * (c + 1)
  let p : ℝ := 1 / 128
  obtain ⟨d₀, hparams⟩ := exists_denseParameter_bundle c
  refine ⟨A, C, p, by norm_num [A], by positivity, by norm_num [p], d₀, ?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD
  let t := denseT c d
  let N := 2 ^ d
  let L := 2^(2*t)*(2^(d+c-t*(c+if Even d then 1 else 0))-1)*
    gaussianBinomial 4 (d/2) t
  let T := N/2-N/2^(t+1)
  let δ := N/2^(2*t)
  let E : ℝ := denseTheta c * (1 - 2 * denseTheta c) * (d : ℝ)^2
  have hp := hparams d hd
  dsimp only at hp
  obtain ⟨hguard, ht2, htd, hDelta, hell, hqexp, h8exp, hlistpow,
    hfieldlow, hfieldhigh⟩ := hp
  obtain ⟨hdeflow, hdefhigh⟩ := denseThreshold_deficit_bounds c d hguard
  have hfinite := denseGold_finite D c d t hB hD ht2 htd hDelta hell hqexp h8exp
  dsimp only at hfinite
  obtain ⟨hlist, F, fieldF, finiteF, hrest⟩ := hfinite
  refine ⟨T, L, ?_, ?_, ?_, hlist, F, fieldF, finiteF, ?_⟩
  · simpa [A, N, T, t, denseTheta] using hdeflow
  · have hC2 : (2 : ℝ) ≤ C := by
      dsimp [C]
      have hc : (0 : ℝ) ≤ c := by positivity
      linarith only [hc]
    have hdense : 1 / 2 - (T : ℝ) / N ≤
        2 * (N : ℝ) ^ (-min (1 / 4) (1 / ((c : ℝ) + 1))) := by
      simpa [N, T, t, denseTheta] using hdefhigh
    exact hdense.trans
      (mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg (by positivity) _))
  · have hLnat : 2 ^ denseGoldExponent c d t ≤ L := by
      dsimp [L]
      exact denseGold_power_le_list c d t htd hDelta
    have hLreal : (2 : ℝ) ^ (denseGoldExponent c d t : ℝ) ≤ (L : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hLnat
    have hx : (2 : ℝ) ^ (E - C * d) ≤
        (2 : ℝ) ^ (denseGoldExponent c d t : ℝ) := by
      simpa [E, C, t, denseTheta] using hlistpow
    exact hx.trans hLreal
  · let := fieldF
    let := finiteF
    obtain ⟨φ, hq, f, g, hcommon, hcountQ, hprobQ⟩ := hrest
    refine ⟨φ, f, g, hcommon, ?_, ?_, ?_, ?_, ?_⟩
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
      have hexp : E - C * d + ((3 + (d - 2 * t) : ℕ) : ℝ) ≤
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
      have hscale : (8 : ℝ) * (δ : ℝ) =
          (2 : ℝ) ^ (((3 + (d - 2 * t) : ℕ) : ℝ)) := by
        rw [hδ, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      have hmul : (2 : ℝ) ^ (E - C * d) * ((8 : ℝ) * δ) ≤
          Fintype.card F := by
        rw [hscale, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hqR]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hden : (0 : ℝ) < 8 * δ := by positivity
      have hxratio : (2 : ℝ) ^ (E - C * d) ≤
          (Fintype.card F : ℝ) / (8 * δ) := (le_div_iff₀ hden).2 hmul
      have h8δ : 8 * δ ≤ Fintype.card F := by
        rw [hq, hδ, ← pow_mul]
        rw [show 8 = 2^3 by norm_num, ← pow_add]
        exact Nat.pow_le_pow_right (by decide) (by simpa [t] using h8exp)
      have hratio1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) / (8 * δ) := by
        exact (le_div_iff₀ hden).2 (by simpa using (show (8 * δ : ℝ) ≤ Fintype.card F by exact_mod_cast h8δ))
      have hratioeq : (Fintype.card F : ℝ) / (4 * δ) =
          2 * ((Fintype.card F : ℝ) / (8 * δ)) := by
        field_simp
        ring
      have hcountR : (Fintype.card F : ℝ) / (4 * δ) - 1 ≤
          (nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T).card := by
        have hcountQ' : (Fintype.card F : ℚ) / (4 * δ) - 1 ≤
            (nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T).card := by
          exact hcountQ
        have hc := (Rat.cast_le (K := ℝ)).2 hcountQ'
        norm_num [Rat.cast_div] at hc
        simpa using hc
      rw [hratioeq] at hcountR
      have hx : (2 : ℝ) ^ (E - C * d) ≤
          2 * ((Fintype.card F : ℝ) / (8 * δ)) - 1 := by
        linarith only [hxratio, hratio1]
      exact hx.trans hcountR
    · have hdt : 2 * t ≤ d := by
        have htd' : t ≤ d / 2 := htd
        omega
      have hδ : δ = 2 ^ (d - 2 * t) := by
        dsimp [δ, N]
        exact Nat.pow_div hdt (by decide)
      obtain ⟨htL, htU⟩ := denseT_real_bounds c d (by omega)
      have hexp : (-7 : ℝ) + (d : ℝ) * (-1 + 2 * denseTheta c) ≤
          -((3 + (d - 2 * t) : ℕ) : ℝ) := by
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
      have hpform : p = (2 : ℝ) ^ (-7 : ℝ) := by
        dsimp [p]
        norm_num [Real.rpow_neg]
      have hinv : (1 : ℝ) / (8 * δ) =
          (2 : ℝ) ^ (-((3 + (d - 2*t) : ℕ) : ℝ)) := by
        rw [hδ, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have htarget : p * (N : ℝ) ^ (-1 + 2 * denseTheta c) ≤
          (1 : ℝ) / (8 * δ) := by
        rw [hpform, hNpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hinv]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have hprobR : (1 : ℝ) / (8 * δ) ≤
          ((nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T).card : ℝ) /
            Fintype.card F := by
        have hprobQ' : (1 : ℚ) / (8 * δ) ≤
            ((nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N/4) f g T).card : ℚ) /
              Fintype.card F := by exact hprobQ
        have hc := (Rat.cast_le (K := ℝ)).2 hprobQ'
        norm_num [Rat.cast_div] at hc
        simpa using hc
      simpa [N, denseTheta] using htarget.trans hprobR
    · have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      rw [hqR]
      simpa [E, C, t, denseTheta] using hfieldlow
    · have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      rw [hqR]
      simpa [E, C, t, denseTheta] using hfieldhigh

    · intro G fieldG finiteG charG ψ hqq
      have hm : 0 < d+c := by omega
      have hround := denseGold_rounding_lower c d t hm hell
      have h2Nq : 2*N ≤ Fintype.card F := by
        rw [hq, ← pow_mul]
        dsimp [N]
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by decide) (hqexp.trans hround.le)
      have hδ : δ = 2 ^ (d-2*t) := by
        dsimp [δ, N]; exact Nat.pow_div (by omega) (by decide)
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hL : Fintype.card F ≤ L := by
        rw [hq, ← pow_mul]
        exact (Nat.pow_le_pow_right (by decide)
          (Nat.mul_div_le (denseGoldExponent c d t) (d+c))).trans
            (denseGold_power_le_list c d t htd hDelta)
      have hqL : Fintype.card F ≤ δ*L := hL.trans (Nat.le_mul_of_pos_left L hδpos)
      obtain ⟨f, g, hc, hg, hf, hcountQ⟩ := denseGold_finite_every_larger_extension
        ψ D c d t (Fintype.card F) hB hD ht2 htd hDelta h2Nq hqL hqq
      refine ⟨f, g, hc, hg, hf, ?_⟩
      have hdt : 2 * t ≤ d := by
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
      have hexp : E - C * d + ((3 + (d - 2 * t) : ℕ) : ℝ) ≤
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
      have hscale : (8 : ℝ) * (δ : ℝ) =
          (2 : ℝ) ^ (((3 + (d - 2 * t) : ℕ) : ℝ)) := by
        rw [hδ, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hqR : (Fintype.card F : ℝ) =
          (2 : ℝ) ^ ((((d+c) * denseGoldExtensionDegree c d t : ℕ) : ℝ)) := by
        rw [hq, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      have hmul : (2 : ℝ) ^ (E - C * d) * ((8 : ℝ) * δ) ≤
          Fintype.card F := by
        rw [hscale, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hqR]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have hδpos : 0 < δ := by rw [hδ]; positivity
      have hden : (0 : ℝ) < 8 * δ := by positivity
      have hxratio : (2 : ℝ) ^ (E - C * d) ≤
          (Fintype.card F : ℝ) / (8 * δ) := (le_div_iff₀ hden).2 hmul
      have h8δ : 8 * δ ≤ Fintype.card F := by
        rw [hq, hδ, ← pow_mul]
        rw [show 8 = 2^3 by norm_num, ← pow_add]
        exact Nat.pow_le_pow_right (by decide) (by simpa [t] using h8exp)
      have hratio1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) / (8 * δ) := by
        exact (le_div_iff₀ hden).2 (by simpa using (show (8 * δ : ℝ) ≤ Fintype.card F by exact_mod_cast h8δ))
      have hratioeq : (Fintype.card F : ℝ) / (4 * δ) =
          2 * ((Fintype.card F : ℝ) / (8 * δ)) := by
        field_simp
        ring
      have hcountR : (Fintype.card F : ℝ) / (4 * δ) - 1 ≤
          (nonzeroBadChallenges (mappedDomain ψ (additiveDomain D)) (N/4) f g T).card := by
        have hcountQ' : (Fintype.card F : ℚ) / (4 * δ) - 1 ≤
            (nonzeroBadChallenges (mappedDomain ψ (additiveDomain D)) (N/4) f g T).card := by
          exact hcountQ
        have hc := (Rat.cast_le (K := ℝ)).2 hcountQ'
        norm_num [Rat.cast_div] at hc
        simpa using hc
      rw [hratioeq] at hcountR
      have hx : (2 : ℝ) ^ (E - C * d) ≤
          2 * ((Fintype.card F : ℝ) / (8 * δ)) - 1 := by
        linarith only [hxratio, hratio1]
      exact hx.trans hcountR

end BinaryFieldCounterexamples
