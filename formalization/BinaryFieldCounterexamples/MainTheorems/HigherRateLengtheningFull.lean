/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.HigherRateLengthening
/-!
# Main theorem companion: the complete higher-rate agreement contract

This companion to [Corollary 5.16, p. 47](../../../binary-field-counterexamples.pdf#page=47)
assembles the two-sided agreement estimate and proves both final numerical
clauses: the limiting agreement is below the Johnson square root, and the
windows cover every rate in `[5/8,1)`. The construction uses the actual decoding
lists and fixed-pair exceptional sets of `PaperSemantics`.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Corollary 5.16's final Johnson comparison, for every permitted dyadic
window: the limiting higher-rate agreement lies below `√rho`. -/
theorem higher_rate_lengthening_lt_sqrt (r : ℕ) (hr : 1 ≤ r) (rho : ℝ)
    (hlo : 1-3*(1/(2^r : ℕ))/4 ≤ rho) (hhi : rho < 1) :
    (1+rho)/2-(1/(2^r : ℕ))/8 < Real.sqrt rho := by
  let u : ℝ := 1/(2^r : ℕ)
  have hu : 0 < u := by dsimp [u]; positivity
  have hup : (2 : ℕ) ≤ 2^r := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
  have huhalf : u ≤ 1/2 := by
    dsimp [u]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hup)
  change 1-3*u/4 ≤ rho at hlo
  change (1+rho)/2-u/8 < Real.sqrt rho
  have hrho : (5 : ℝ)/8 ≤ rho := by linarith
  have hs : (Real.sqrt rho)^2 = rho := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
  have hslo : (3 : ℝ)/4 < Real.sqrt rho := by nlinarith
  have hsup : Real.sqrt rho < 1 := by nlinarith
  have hgap : (1-Real.sqrt rho)*(1+Real.sqrt rho) ≤ 3*u/4 := by nlinarith
  have hgsmall : 0 ≤ 1-Real.sqrt rho := by linarith
  have hgupper : 1-Real.sqrt rho < 3*u/7 := by nlinarith
  have hgsq : (1-Real.sqrt rho)^2 < (3*u/7)^2 := by nlinarith
  have husq : u^2 ≤ u/2 := by nlinarith
  nlinarith

/-- Corollary 5.16's coverage clause: its windows with `r ≥ 1` cover the
entire interval `[5/8,1)`, including the left endpoint. -/
theorem higher_rate_lengthening_rate_coverage (rho : ℝ)
    (hlo : (5 : ℝ)/8 ≤ rho) (hhi : rho < 1) :
    ∃ r : ℕ, 1 ≤ r ∧ 1-3*(1/(2^r : ℕ))/4 ≤ rho ∧
      rho < 1-(1/(2^r : ℕ))/4 := by
  have hg : 0 < 1-rho := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1/(4*(1-rho)))
  have hn' : 1/(4*(1-rho)) < ((2^(n+1) : ℕ) : ℝ) := by
    exact hn.trans_le (by exact_mod_cast (n.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ n))).le)
  have hex : ∃ r : ℕ, 1 ≤ r ∧ 1/(2^r : ℕ) < 4*(1-rho) := by
    refine ⟨n+1, by omega, ?_⟩
    exact (div_lt_iff₀ (by positivity)).mpr
      (by have hh := (div_lt_iff₀ (by positivity : 0 < 4*(1-rho))).mp hn'; nlinarith)
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  refine ⟨r, hr.1, ?_, by linarith [hr.2]⟩
  by_cases heq : r = 1
  · rw [heq]
    norm_num
    exact hlo
  · have hrprev : 1 ≤ r-1 := by omega
    have hprev := Nat.find_min hex (show r-1 < Nat.find hex by dsimp [r]; omega)
    have hpre : 4*(1-rho) ≤ 1/(2^(r-1) : ℕ) := by
      exact le_of_not_gt (fun h => hprev ⟨hrprev,h⟩)
    have hp : 2^r = (2^(r-1) : ℕ)*2 := by
      rw [← pow_succ, Nat.sub_add_cancel hr.1]
    have hu : (1 : ℝ)/((2^(r-1) : ℕ) : ℝ) = 2*((1 : ℝ)/((2^r : ℕ) : ℝ)) := by
      rw [hp, Nat.cast_mul, Nat.cast_ofNat]
      field_simp
    rw [hu] at hpre
    linarith


/-- Corollary 5.16 with the complete two-sided agreement contract. The same
literal decoding list and fixed pair attain a threshold between the limiting
curve minus `epsilon` and the curve itself. Constants are fixed before the
rate and accuracy, and all individual and common agreement equalities and
quasipolynomial bounds of the original theorem are preserved. -/
theorem higher_rate_lengthening_full (c r : ℕ) (hr : 1 ≤ r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ rho : ℝ, 1-3*(1/(2^r : ℕ))/4 ≤ rho → rho < 1-(1/(2^r : ℕ))/4 →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [CharP B 2],
      Fintype.card B = 2^(d+c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2^d →
    let N : ℕ := 2^d
    let J := ⌊rho*(N : ℝ)⌋₊
    ∃ T L : ℕ,
      (1+rho)/2-(1/(2^r : ℕ))/8-epsilon ≤ (T : ℝ)/N ∧
      (T : ℝ)/N ≤ (1+rho)/2-(1/(2^r : ℕ))/8 ∧
      (N : ℝ)^(A*Real.log N) ≤ L ∧ ordinaryList (additiveDomain D) J T L ∧
    ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      let := fieldF
      let := finiteF
      ∃ phi : B →+* F, ∃ f g : mappedDomain phi (additiveDomain D) → F,
        agreementEQ (mappedDomain phi (additiveDomain D)) J f J ∧
        agreementEQ (mappedDomain phi (additiveDomain D)) J g J ∧
        commonAgreementEQ (mappedDomain phi (additiveDomain D)) J f g J ∧
        L ≤ (nonzeroBadChallenges (mappedDomain phi (additiveDomain D)) J f g T).card ∧
        (Fintype.card F : ℝ) ≤ (N : ℝ)^(C*Real.log N) := by
  obtain ⟨A,C,hA,hC,hconstruction⟩ := higher_rate_lengthening c r hr
  refine ⟨A,C,hA,hC,?_⟩
  intro rho hlo hhi epsilon hepsilon
  obtain ⟨dSeed,hSeed⟩ := hconstruction rho hlo hhi (epsilon/2) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (2/epsilon)
  refine ⟨max dSeed n,?_⟩
  intro d hd B fieldB finiteB charB hB D hD
  obtain ⟨T0,L,hT0,hL,hlist,F,fieldF,finiteF,phi,f,g,hf,hg,hfg,hbad,hfield⟩ :=
    hSeed d ((le_max_left _ _).trans hd) B hB D hD
  let := fieldF
  let := finiteF
  let N : ℕ := 2^d
  let U : ℝ := (1+rho)/2-(1/(2^r : ℕ))/8
  let T : ℕ := min T0 ⌊U*N⌋₊
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hnN : (n : ℝ) < N := by
    exact_mod_cast n.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ((le_max_right _ _).trans hd))
  have hsmall : 1/(N : ℝ) < epsilon/2 := by
    have hh := (div_lt_iff₀ hepsilon).mp (hn.trans hnN)
    apply (div_lt_iff₀ hN).mpr
    nlinarith
  have hp : (2 : ℕ) ≤ 2^r := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
  have hu : (1 : ℝ)/(2^r : ℕ) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hfloor : U-1/(N : ℝ) ≤ (⌊U*N⌋₊ : ℝ)/N := by
    apply (le_div_iff₀ hN).mpr
    have hh := (Nat.sub_one_lt_floor (U*N)).le
    field_simp
    nlinarith

  -- Lower the threshold if needed; this leaves the actual lists and pair intact.
  have hTle : T ≤ T0 := Nat.min_le_left _ _
  have hTlower : U-epsilon ≤ (T : ℝ)/N := by
    dsimp [T]
    rw [Nat.cast_min, ← min_div_div_right hN.le]
    exact le_min (by change U-epsilon/2 ≤ (T0 : ℝ)/N at hT0; linarith)
      (by linarith)
  have hTupper : (T : ℝ)/N ≤ U := by
    apply (div_le_iff₀ hN).mpr
    have hcast : (T : ℝ) ≤ (⌊U*N⌋₊ : ℝ) := by
      exact_mod_cast Nat.min_le_right T0 ⌊U*N⌋₊
    exact hcast.trans (Nat.floor_le (mul_nonneg hU hN.le))
  have hlist' : ordinaryList (additiveDomain D) ⌊rho*(N : ℝ)⌋₊ T L := by
    obtain ⟨w,ps,hps,hagree⟩ := hlist
    exact ⟨w,ps,hps,fun p hp => ⟨(hagree p hp).1,hTle.trans (hagree p hp).2⟩⟩
  have hsubset : nonzeroBadChallenges (mappedDomain phi (additiveDomain D))
      ⌊rho*(N : ℝ)⌋₊ f g T0 ⊆ nonzeroBadChallenges
      (mappedDomain phi (additiveDomain D)) ⌊rho*(N : ℝ)⌋₊ f g T := by
    intro z hz
    simp only [nonzeroBadChallenges, Finset.mem_erase, badChallenges,
      Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hnz,p,hdegree,hagree⟩ := hz
    exact ⟨hnz,p,hdegree,hTle.trans hagree⟩
  exact ⟨T,L,hTlower,hTupper,hL,hlist',F,fieldF,finiteF,phi,f,g,hf,hg,hfg,
    hbad.trans (Finset.card_le_card hsubset),hfield⟩

end BinaryFieldCounterexamples
