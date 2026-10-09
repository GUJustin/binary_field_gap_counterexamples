/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.DenseHalfRate
public import BinaryFieldCounterexamples.MainTheorems.DenseSmallCodimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Discussion and introduction consequences of the dense Gold theorems

The discussion restates Corollary 5.15 as superpolynomial exceptional counts
at half rate with agreement approaching `5/8`. The first theorem makes
both assertions simultaneous for the actual received pair: for any fixed
power `b` and any positive tolerance, every sufficiently large prescribed
dense domain admits a pair whose count exceeds `N^b` and whose agreement
fraction is within that tolerance below `5/8`.

The introduction's full-field example after Corollary 5.2 measures its
Johnson deficit in both coordinates and agreement fraction. The final theorem
retains the actual quarter-rate pair while converting the existing fractional
bounds to two-sided multiples of `N^(3/4)` coordinates.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Filter

/-- Discussion, lines 23--25: Corollary 5.15 supplies superpolynomial counts
while agreement approaches `5/8`, for the same half-rate pair with common
agreement exactly `1/2`. The cutoff precedes every prescribed dense domain. -/
theorem discussion_half_rate_superpolynomial_limit (c : ℕ) (b ε : ℝ)
    (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d →
    ∀ a : B,
    let N : ℕ := 2^d
    ∃ T : ℕ, 0 < 5/8-(T:ℝ)/N ∧ 5/8-(T:ℝ)/N < ε ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (affineDomain (additiveDomain D) a)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N/2) f g (N/2) ∧
        (N:ℝ)^b < (nonzeroBadChallenges D' (N/2) f g T).card := by
  let θ : ℝ := min (1/4) (1/((c:ℝ)+1))
  let α : ℝ := θ*(1-2*θ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθu : θ ≤ 1/4 := min_le_left _ _
  have hα : 0 < α := mul_pos hθ (by linarith)
  obtain ⟨A,C,p,hA,hC,hp,d₁,hpair⟩ := gold_half_rate_dense_asymptotic c
  change ∀ d : ℕ, d₁ ≤ d → _ at hpair

  -- The normalized deficit vanishes along the actual lengths `N=2^d`.
  have hlim : Tendsto (fun d : ℕ => ((2:ℝ)^d)^(-θ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hθ).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have hev : ∀ᶠ d : ℕ in atTop, C*((2:ℝ)^d)^(-θ) < ε := by
    have hzero : C*0 < ε := by simpa only [mul_zero] using hε
    have hh := (hlim.const_mul C).eventually (eventually_lt_nhds hzero)
    simpa only [mul_zero] using hh
  obtain ⟨d₂,hd₂⟩ := eventually_atTop.mp hev

  -- The positive quadratic exponent eventually exceeds any fixed linear one.
  obtain ⟨d₃,hd₃⟩ := exists_nat_gt ((C+b+1)/α)
  refine ⟨max d₁ (max d₂ (max 1 d₃)),?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD a
  have hd₁ : d₁ ≤ d := (le_max_left _ _).trans hd
  have hd₂d : d₂ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd₃d : d₃ ≤ d := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hd1 : 1 ≤ d := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  have hscale : C+b+1 < α*(d:ℝ) := by
    have hh : (C+b+1)/α < (d:ℝ) :=
      hd₃.trans_le (by exact_mod_cast hd₃d)
    simpa only [mul_comm] using (div_lt_iff₀ hα).mp hh
  have hexp : (d:ℝ)*b < α*(d:ℝ)^2-C*d := by
    have hh : 0 < (d:ℝ)*(α*(d:ℝ)-C-b) := mul_pos hdR (by linarith)
    nlinarith
  obtain ⟨T,hlo,hhi,hgaplo,hgaphi,F,fieldF,finiteF,hrest⟩ :=
    hpair d hd₁ B hB D hD a
  refine ⟨T,?_,?_,F,fieldF,finiteF,?_⟩
  · have hpos : 0 < A*((2^d:ℕ):ℝ)^(-θ) := by positivity
    exact hpos.trans_le hlo
  · exact hhi.trans_lt (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hd₂ d hd₂d)
  · let := fieldF
    let := finiteF
    obtain ⟨φ,f,g,hcommon,hcount,hprob,hfieldlo,hfieldhi⟩ := hrest
    refine ⟨φ,f,g,hcommon,?_⟩
    have hpower : (((2^d:ℕ):ℝ))^b = (2:ℝ)^((d:ℝ)*b) := by
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,
        ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [hpower]
    have hstrict := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hexp
    exact hstrict.trans_le hcount

/-- Introduction, line 341: on a full binary field the quarter-rate dense
Gold example lies below Johnson by `Θ(N^(3/4))` coordinates, equivalently
`Θ(N^(-1/4))` in agreement fraction. Both bounds concern the same actual pair. -/
theorem introduction_full_field_johnson_deficit :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∃ d₀ : ℕ,
    ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2^d →
    let N : ℕ := 2^d
    ∃ T : ℕ,
      A*(N:ℝ)^(-(1/4:ℝ)) ≤ 1/2-(T:ℝ)/N ∧
      1/2-(T:ℝ)/N ≤ C*(N:ℝ)^(-(1/4:ℝ)) ∧
      A*(N:ℝ)^(3/4:ℝ) ≤ (N:ℝ)/2-T ∧
      (N:ℝ)/2-T ≤ C*(N:ℝ)^(3/4:ℝ) ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (additiveDomain (⊤ : AddSubgroup B))
      ∃ f g : D' → F,
        commonAgreementEQ D' (N/4) f g (N/4) ∧
        (2:ℝ)^((1/8)*(d:ℝ)^2-C*d) ≤
          (nonzeroBadChallenges D' (N/4) f g T).card := by
  obtain ⟨A,C,p,hA,hC,hp,d₀,h⟩ :=
    superpolynomial_near_johnson_small_codimension 0 (by omega)
  refine ⟨A,C,hA,hC,d₀,?_⟩
  intro d hd B fieldB finiteB decB charB hB
  have hD : (additiveDomain (⊤ : AddSubgroup B)).card = 2^d := by
    simpa [additiveDomain] using hB
  obtain ⟨halphabet,T,L,hlo,hhi,hlistcount,hlist,F,fieldF,finiteF,hrest⟩ :=
    h d hd B (by simpa using hB) ⊤ hD
  refine ⟨T,hlo,hhi,?_,?_,F,fieldF,finiteF,?_⟩
  · have hN : (0:ℝ) < (2^d:ℕ) := by positivity
    have hh := mul_le_mul_of_nonneg_right hlo hN.le
    have heq : (((2^d:ℕ):ℝ))^(-(1/4:ℝ))*((2^d:ℕ):ℝ) =
        (((2^d:ℕ):ℝ))^(3/4:ℝ) := by
      rw [←Real.rpow_add_one hN.ne']
      norm_num
    rw [mul_assoc,heq] at hh
    convert hh using 1
    field_simp
  · have hN : (0:ℝ) < (2^d:ℕ) := by positivity
    have hh := mul_le_mul_of_nonneg_right hhi hN.le
    have heq : (((2^d:ℕ):ℝ))^(-(1/4:ℝ))*((2^d:ℕ):ℝ) =
        (((2^d:ℕ):ℝ))^(3/4:ℝ) := by
      rw [←Real.rpow_add_one hN.ne']
      norm_num
    rw [mul_assoc,heq] at hh
    convert hh using 1
    field_simp
  · let := fieldF
    let := finiteF
    obtain ⟨φ,f,g,hcommon,hcount,hprob,hfieldlo,hfieldhi⟩ := hrest
    exact ⟨φ,f,g,hcommon,hcount⟩
end BinaryFieldCounterexamples
