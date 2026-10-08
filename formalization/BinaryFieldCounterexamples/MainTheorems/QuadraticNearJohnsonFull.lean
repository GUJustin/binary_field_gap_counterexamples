/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonExact
public import BinaryFieldCounterexamples.MainTheorems.QuadraticNearJohnsonCompanions
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.DecodingLists
public import BinaryFieldCounterexamples.Constructions.QuadraticNearJohnson.ThresholdArithmetic

/-!
# Main theorem 4.1 with its decoding list for the same first input

[Theorem 4.1, pp. 28–30](../../../binary-field-counterexamples.pdf#page=28)
has an exact quadratic exceptional population on every prescribed binary
additive domain of size `N = 16K`. The paragraph after its proof also asserts
that the very same first input has `M = (N−1)(N−2)/6` distinct codewords at
message length `2K = N/8`. This companion assembles the exceptional profile
and that list. Every listed polynomial has exact degree `2K−1` and agrees
with the literal first input on exactly `4K−1` coordinates.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
open Polynomial QuadraticConstruction

/-- Theorem 4.1 and its rate-`1/8` decoding-list paragraph, assembled for one
fixed pair: the exact exceptional profile and the list refer to the same `f`.
The codewords have exact degree `2K−1`, hence strict degree below `N/8`. -/
theorem quadratic_near_johnson_exact_with_decoding_list
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hproper : ¬Function.Surjective φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := mappedDomain φ (additiveDomain D)
    ∃ f g : E → F, ∃ I : Finset F, ∃ ps : Finset F[X],
      commonAgreementEQ E K f g (2 * K - 1) ∧
      agreementLE E K f (2 * K) ∧ agreementEQ E K g (2 * K - 1) ∧
      I.card = (16 * K - 1) * (16 * K - 2) / 6 ∧ 0 ∉ I ∧
      (∀ T : ℕ, 2 * K + 1 ≤ T → T ≤ 4 * K - 1 → badChallenges E K f g T = I) ∧
      (∀ z ∈ I, agreementEQ E K (fun x => f x + z * g x) (4 * K - 1)) ∧
      badChallenges E K f g (4 * K) = ∅ ∧
      ps.card = I.card ∧
      (∀ p ∈ ps, p.degree = (2 * K - 1 : ℕ) ∧ p.degree < (2 * K : ℕ) ∧
        agreementCount E f p = 4 * K - 1) := by
  classical
  let : Algebra B F := φ.toAlgebra
  have hex : ∃ θ : F, θ ∉ Set.range φ := by
    simpa only [Function.Surjective, not_forall, Set.mem_range] using hproper
  obtain ⟨θ, hθ⟩ := hex
  obtain ⟨s, hs⟩ := exists_quadratic_source_shift D K (by omega) hpow hD θ hθ
  let E := mappedDomain φ (additiveDomain D)
  let f : E → F := fun x => firstWord K θ x + φ s * secondWord K (x : F)
  let g : E → F := fun x => secondWord K (x : F)
  have hf : agreementLE E K f (2 * K) := hs
  obtain ⟨hc, hg⟩ := canonical_quadratic_source_agreement φ D K hK hpow hD θ (φ s)
  obtain ⟨I, hI, hT, hmax, hempty⟩ :=
    quadratic_shifted_exact_challenges φ θ hθ D K hK hpow hD (φ s)
  have hzero : 0 ∉ I := by
    intro hz
    have hbad : 0 ∈ badChallenges E K f g (4 * K - 1) := by
      rw [hT (4 * K - 1) (by omega) le_rfl]
      exact hz
    obtain ⟨p, hp, hcount⟩ := (mem_badChallenges E K f g (4 * K - 1) 0).mp hbad
    simp only [zero_mul, add_zero] at hcount
    change 4 * K - 1 ≤ agreementCount E f p at hcount
    have hu := hf p hp
    omega

  -- The direction is the literal monomial from the construction. Its high
  -- coefficient recovers each nonzero challenge in the decoding list.
  have hmono : ∀ z ∈ I,
      agreementEQ E K (fun x => f x + z * (X ^ (2 * K - 1) : F[X]).eval (x : F))
        (4 * K - 1) := by
    simpa only [eval_pow, eval_X, E, f, g, secondWord] using hmax
  obtain ⟨ps, hps, hpolys⟩ := exact_list_of_nonzero_polynomial_direction E K
    (2 * K - 1) (4 * K - 1) f (X ^ (2 * K - 1)) (monic_X_pow _)
    (degree_X_pow _) (by omega) I hzero hmono
  refine ⟨f, g, I, ps, hc, hf, hg, hI, hzero, hT, hmax, hempty, hps, ?_⟩
  intro p hp
  obtain ⟨hdeg, hlt, hcount⟩ := hpolys p hp
  exact ⟨hdeg, by simpa only [show 2 * K - 1 + 1 = 2 * K by omega] using hlt, hcount⟩

/-- Corollary 4.2 with both “in particular” clauses assembled for the same
explicit monomial pair and the same scalar `θ`: `q≥M` yields strictly more
than `M/2` challenges, and `q>choose M 2` yields all `M` counted challenges. -/
theorem quadratic_near_johnson_same_field_full
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (D : AddSubgroup F) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := additiveDomain D
    let M : ℕ := (16 * K - 1) * (16 * K - 2) / 6
    let q : ℕ := Fintype.card F
    ∃ θ : F,
      let f : E → F := fun x => (x : F) ^ (8 * K - 1) + θ * (x : F) ^ (4 * K - 1)
      let g : E → F := fun x => (x : F) ^ (2 * K - 1)
      commonAgreementEQ E K f g (2 * K - 1) ∧
      max (M - ⌊(Nat.choose M 2 : ℚ) / q⌋₊)
        ⌈(q : ℚ) * M / (q + M - 1)⌉₊ ≤
        (badChallenges E K f g (4 * K - 1)).card ∧
      (M ≤ q → (M : ℚ) / 2 < (badChallenges E K f g (4 * K - 1)).card) ∧
      (Nat.choose M 2 < q → M ≤ (badChallenges E K f g (4 * K - 1)).card) := by
  classical
  let M : ℕ := (16 * K - 1) * (16 * K - 2) / 6
  let q : ℕ := Fintype.card F
  obtain ⟨θ, hc, hb⟩ := quadratic_near_johnson_same_field D K hK hpow hD
  refine ⟨θ, hc, hb, ?_, ?_⟩
  · intro hqM
    have hM : 0 < M := by
      apply Nat.div_pos
      · have h1 : 31 ≤ 16 * K - 1 := by omega
        have h2 : 30 ≤ 16 * K - 2 := by omega
        exact (by norm_num : 6 ≤ 31 * 30).trans (Nat.mul_le_mul h1 h2)
      · norm_num
    have hhalf := quadratic_collision_ceiling_gt_half M q hM hqM
    have hceil := (le_max_right _ _).trans hb
    exact hhalf.trans_le (Nat.cast_le.mpr hceil)
  · intro hq
    have hfloor := quadratic_collision_floor_eq_zero M q hq
    have hloss := (le_max_left _ _).trans hb
    change M - ⌊(Nat.choose M 2 : ℚ) / q⌋₊ ≤ _ at hloss
    rwa [hfloor] at hloss

/-- Theorem 4.1's Johnson-placement paragraph and the subspace-locator
summary: on the actual prescribed domain one fixed pair has exactly `M`
nonzero challenges at the largest integer below Johnson, with common-agreement
gap exactly `N/8−2`. -/
theorem quadratic_near_johnson_at_largest_below_johnson
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (hproper : ¬Function.Surjective φ)
    (D : AddSubgroup B) (K : ℕ) (hK : 2 ≤ K)
    (hpow : ∃ k : ℕ, K = 2 ^ k) (hD : (additiveDomain D).card = 16 * K) :
    let E := mappedDomain φ (additiveDomain D)
    let T : ℕ := 4 * K - 3
    ∃ f g : E → F,
      commonAgreementEQ E K f g (2 * K - 1) ∧
      agreementLE E K f (2 * K) ∧ agreementEQ E K g (2 * K - 1) ∧
      (badChallenges E K f g T).card = (16 * K - 1) * (16 * K - 2) / 6 ∧
      0 ∉ badChallenges E K f g T ∧
      (∀ z ∈ badChallenges E K f g T,
        agreementEQ E K (fun x => f x + z * g x) (4 * K - 1)) ∧
      ((T : ℝ) < Real.sqrt ((16 * K * (K - 1) : ℕ) : ℝ)) ∧
      (∀ m : ℕ, (m : ℝ) < Real.sqrt ((16 * K * (K - 1) : ℕ) : ℝ) ↔ m ≤ T) ∧
      T - (2 * K - 1) = (16 * K) / 8 - 2 := by
  classical
  obtain ⟨f, g, I, hc, hf, hg, hI, hzero, hT, hmax, _⟩ :=
    quadratic_near_johnson_exact φ hproper D K hK hpow hD
  have hbad := hT (4 * K - 3) (by omega) (by omega)
  obtain ⟨hlo, _, hlargest, hgap, hgapN⟩ :=
    quadratic_johnson_largest_integer_and_gap K hK
  refine ⟨f, g, hc, hf, hg, ?_, ?_, ?_, hlo, hlargest, hgap.trans hgapN⟩
  · rw [hbad]
    exact hI
  · rw [hbad]
    exact hzero
  · rw [hbad]
    exact hmax

end BinaryFieldCounterexamples
