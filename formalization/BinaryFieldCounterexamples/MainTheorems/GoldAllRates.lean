/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.Constructions.GoldAllRates.GoldAssembly
public import BinaryFieldCounterexamples.Constructions.GoldAllRates.RateBounds
/-!
# Main theorem: every fixed rate on every dense binary domain

Paper statement: [Corollary 5.17, p. 48](../../../binary-field-counterexamples.pdf#page=48),
“Every fixed rate on every dense binary domain”. Public theorems:
`BinaryFieldCounterexamples.gold_all_rates` and
`BinaryFieldCounterexamples.gold_all_rates_translate`. **Proved.**

Fix the ambient codimension `c` and a positive integer `r`. Constants `A,C>0`
are chosen before the rate, accuracy, dimension, field and prescribed domain.
For `0<rho<1` with `2^(-r-2)<min(rho,(1-rho)/3)`, every sufficiently large
binary `d`-space in a field of size `2^(d+c)` has a decoding list of at least
`N^(A*log N)` distinct strict-degree-`floor(rho*N)` polynomials. Its agreement
threshold satisfies
`rho+2^(-r-2)-epsilon ≤ T/N ≤ rho+2^(-r-2)`.

Over an actual finite extension of size at most `N^(C*log N)`, one fixed pair
has both individual agreements and common agreement exactly `floor(rho*N)`,
and at least the same number of distinct nonzero exceptional challenges at
threshold `T`. All conclusions also hold on every translate of the domain.

The construction does not need the corollary's additional square-root
hypothesis. `gold_all_rates_limiting_fraction` proves separately that this
hypothesis places the limiting agreement strictly between `rho` and `sqrt rho`.
The dimension cutoff absorbs all dependencies on the fixed parameters; no extra
restriction on the paper's sufficiently-large-dimension quantifier is imposed.

The proof reuses the dense Gold seed, disjoint locator multiplication and the
separating-pole extension construction. Only padding outside the seed domain
is needed, so balanced padding and concentration estimates are absent. All
mathematical dependencies are proved, with no admitted components.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
open Filter
open scoped Topology
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The square-root hypothesis in Corollary 5.17 places the limiting agreement
fraction strictly above the input rate and strictly below the Johnson fraction. -/
theorem gold_all_rates_limiting_fraction (r : ℕ) (rho : ℝ)
    (hroot : 1/(2^(r+2) : ℕ) < Real.sqrt rho-rho) :
    rho < rho+1/(2^(r+2) : ℕ) ∧ rho+1/(2^(r+2) : ℕ) < Real.sqrt rho := by
  have hpos : (0 : ℝ) < 1/(2^(r+2) : ℕ) := by positivity
  constructor <;> linarith

/-- Corollary 5.17 on every translate of each prescribed dense additive domain.
Constants depend only on `c,r`, and are fixed before `rho,epsilon,d,B,D,a`.
The cutoff may depend on the rate and accuracy. The extra square-root condition
is unnecessary for construction; see `gold_all_rates_limiting_fraction`. -/
theorem gold_all_rates_translate (c r : ℕ) (_hr : 1 ≤ r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ rho : ℝ, 0 < rho → rho < 1 →
      1/(2^(r+2) : ℕ) < rho → 1/(2^(r+2) : ℕ) < (1-rho)/3 →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d → ∀ a : B,
    let N : ℕ := 2^d
    let J := ⌊rho*(N : ℝ)⌋₊
    ∃ T L : ℕ,
      rho+1/(2^(r+2) : ℕ)-epsilon ≤ (T : ℝ)/N ∧
      (T : ℝ)/N ≤ rho+1/(2^(r+2) : ℕ) ∧
      (N : ℝ)^(A*Real.log N) ≤ L ∧
      ordinaryList (affineDomain (additiveDomain D) a) J T L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ phi : B →+* F,
      ∃ f g : mappedDomain phi (affineDomain (additiveDomain D) a) → F,
        agreementEQ (mappedDomain phi (affineDomain (additiveDomain D) a)) J f J ∧
        agreementEQ (mappedDomain phi (affineDomain (additiveDomain D) a)) J g J ∧
        commonAgreementEQ (mappedDomain phi (affineDomain (additiveDomain D) a)) J f g J ∧
        L ≤ (nonzeroBadChallenges
          (mappedDomain phi (affineDomain (additiveDomain D) a)) J f g T).card ∧
        (Fintype.card F : ℝ) ≤ (N : ℝ)^(C*Real.log N) := by
  let theta : ℝ := min (1/4) (1/((c+r : ℕ)+1))
  let alpha : ℝ := theta*(1-2*theta)
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have hthetaU : theta ≤ 1/4 := min_le_left _ _
  have halpha : 0 < alpha := mul_pos htheta (by linarith)
  have halphaU : alpha ≤ 1 := by dsimp [alpha]; linarith [sq_nonneg theta]
  obtain ⟨C,hC,dSeed,hconstruction⟩ := GoldAllRates.gold_outside_padding_finite c r
  obtain ⟨hA,dList,hList⟩ :=
    HigherRateLengthening.selected_list_bounds alpha C halpha halphaU hC.le r
  refine ⟨alpha/8/(2*Real.log 2),32/Real.log 2,hA,by positivity,?_⟩
  intro rho hrhopos hrholt hrholow hrhocomp epsilon hepsilon

  -- One cutoff covers the seed, list growth, exact quarter size and vanishing errors.
  have hevent := (GoldAllRates.all_rates_error_tendsto C theta htheta r).eventually
    (gt_mem_nhds hepsilon)
  obtain ⟨dError,hError⟩ := Filter.eventually_atTop.mp hevent
  let d0 := max (max (dSeed+r) dList) (max dError (max c (r+2)))
  refine ⟨d0,?_⟩
  intro d hd B fieldB finiteB charB hB D hD a
  have hdSeed : dSeed+r ≤ d := (le_max_left _ _).trans ((le_max_left _ _).trans hd)
  have hdList : dList ≤ d := (le_max_right _ _).trans ((le_max_left _ _).trans hd)
  have hdError : dError ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdC : c ≤ d := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hdr : r+2 ≤ d := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  let N : ℕ := 2^d
  let M : ℕ := 2^(d-r)
  let J := ⌊rho*(N : ℝ)⌋₊
  let L : ℕ := 2^⌊alpha/8*(d : ℝ)^2⌋₊
  obtain ⟨hK,hJ,hw,hMN⟩ :=
    GoldAllRates.rate_parameters r d hdr rho hrhopos hrholt hrholow hrhocomp
  obtain ⟨hrd,hLupper,hLlower,hLseed⟩ := hList d hdList
  rw [←Nat.cast_sub hrd] at hLseed

  -- Construct the actual decoding list and the single pair on the translated domain.
  obtain ⟨T0,hhalf,hseed,hdomains⟩ :=
    hconstruction d hdSeed (by omega) hdC B hB D hD J L hK hJ hw hLupper hLseed
  obtain ⟨hordinary,F,fieldF,finiteF,phi,f,g,hf,hg,hfg,hbad,hfield⟩ := hdomains a
  let := fieldF
  let := finiteF
  -- The exact threshold is the requested limit minus seed and floor errors.
  have hfloorL : rho*(N : ℝ)-1 ≤ (J : ℝ) := (Nat.sub_one_lt_floor _).le
  have hfloorU : (J : ℝ) ≤ rho*(N : ℝ) := Nat.floor_le (by positivity)
  have hquarter := HigherRateLengthening.seed_quarter_cast r d hdr
  have hbounds := GoldAllRates.normalized_agreement_bounds N M J T0 rho
    (C*(M : ℝ)^(-theta)) (by dsimp [N]; positivity) (by dsimp [M]; positivity)
    hMN hK hquarter (by positivity) hseed hhalf hfloorL hfloorU
  have hqratio := GoldAllRates.seed_quarter_ratio r d hdr
  have hquarterratio : ((M : ℝ)/N)/4 = 1/(2^(r+2) : ℕ) := by
    rw [←hqratio, hquarter]
    ring
  dsimp only at hbounds
  rw [hquarterratio] at hbounds
  refine ⟨J-M/4+T0,L,?_,hbounds.2,hLlower,hordinary,
    F,fieldF,finiteF,phi,f,g,hf,hg,hfg,hbad,hfield⟩
  have herr := hError d hdError
  change C*(M : ℝ)^(-theta)+1/(N : ℝ) < epsilon at herr
  linarith [hbounds.1]

/-- Corollary 5.17: every fixed admissible rate on every prescribed dense
additive domain. Constants are fixed before the rate and accuracy, and the
agreement has both the asymptotic lower bound and the exact limiting upper
bound. The square-root hypothesis is only needed for the separate limiting
fraction theorem, so this construction has a slightly stronger parameter range. -/
theorem gold_all_rates (c r : ℕ) (hr : 1 ≤ r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ rho : ℝ, 0 < rho → rho < 1 →
      1/(2^(r+2) : ℕ) < rho → 1/(2^(r+2) : ℕ) < (1-rho)/3 →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d →
    let N : ℕ := 2^d
    let J := ⌊rho*(N : ℝ)⌋₊
    ∃ T L : ℕ,
      rho+1/(2^(r+2) : ℕ)-epsilon ≤ (T : ℝ)/N ∧
      (T : ℝ)/N ≤ rho+1/(2^(r+2) : ℕ) ∧
      (N : ℝ)^(A*Real.log N) ≤ L ∧ ordinaryList (additiveDomain D) J T L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ phi : B →+* F, ∃ f g : mappedDomain phi (additiveDomain D) → F,
        agreementEQ (mappedDomain phi (additiveDomain D)) J f J ∧
        agreementEQ (mappedDomain phi (additiveDomain D)) J g J ∧
        commonAgreementEQ (mappedDomain phi (additiveDomain D)) J f g J ∧
        L ≤ (nonzeroBadChallenges (mappedDomain phi (additiveDomain D)) J f g T).card ∧
        (Fintype.card F : ℝ) ≤ (N : ℝ)^(C*Real.log N) := by
  obtain ⟨A,C,hA,hC,htranslate⟩ := gold_all_rates_translate c r hr
  refine ⟨A,C,hA,hC,?_⟩
  intro rho hrhopos hrholt hrholow hrhocomp epsilon hepsilon
  obtain ⟨d0,hd0⟩ := htranslate rho hrhopos hrholt hrholow hrhocomp epsilon hepsilon
  refine ⟨d0,?_⟩
  intro d hd B fieldB finiteB charB hB D hD
  have hzero : affineDomain (additiveDomain D) (0 : B) = additiveDomain D := by
    simp [affineDomain]
  have hresult := hd0 d hd B hB D hD 0
  rw [hzero] at hresult
  exact hresult

end BinaryFieldCounterexamples
