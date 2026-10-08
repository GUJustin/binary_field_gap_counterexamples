/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.MainTheorems.AllRatesCertainFailureFull
public import BinaryFieldCounterexamples.Constructions.AllRates.PolynomialCountConsequences

/-!
# Main theorem companion: polynomial exceptional populations at every rate

This proves the “in particular” clause of Theorem 4.5 (p. 33) and the following
paragraph (p. 33). For fixed rate and exponent, one threshold below Johnson,
one positive constant and one cutoff work uniformly over all sufficiently
large binary domains. When `q ≥ N^s`, the actual nonzero exceptional set has
at least `c N^s` elements. The same guarantee holds with both inputs far when
an intermediate proper field has at least `N^s` elements; no extension degree
beyond properness is required, so quadratic extensions are included.
Taking `s=2` yields the asserted quadratic lower bound at every fixed rate.
-/

@[expose] public section
namespace BinaryFieldCounterexamples
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4.5's “in particular” and the following paragraph: actual
exceptional sets have uniformly at least `c N^s` nonzero challenges under the
large challenge-field or large intermediate-field hypotheses, respectively.
In particular the first clause with `s=2` gives order `N²` at every fixed rate. -/
theorem all_rates_certain_failure_polynomial_count
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) (s : ℕ) (hs : 2 ≤ s) :
    ∃ α c : ℝ, ρ < α ∧ α < Real.sqrt ρ ∧ 0 < c ∧ ∃ N₀ : ℕ,
      (∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
        (D : AddSubgroup F), N₀ ≤ (additiveDomain D).card →
        ((additiveDomain D).card : ℝ)^s ≤ Fintype.card F →
        let S := additiveDomain D
        let J := ⌊ρ * S.card⌋₊
        ∃ f g : S → F, agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
          c * (S.card : ℝ)^s ≤
            (nonzeroBadChallenges S J f g ⌈α * S.card⌉₊).card) ∧
      (∀ (B F : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2]
        [Field F] [Fintype F] [DecidableEq F] (φ : B →+* F)
        (D : AddSubgroup B), N₀ ≤ (additiveDomain D).card →
        Fintype.card B < Fintype.card F →
        ((additiveDomain D).card : ℝ)^s ≤ Fintype.card B →
        let S := mappedDomain φ (additiveDomain D)
        let J := ⌊ρ * S.card⌋₊
        ∃ f g : S → F,
          agreementEQ S J f J ∧ agreementEQ S J g J ∧
          commonAgreementEQ S J f g J ∧
          c * (S.card : ℝ)^s ≤
            (nonzeroBadChallenges S J f g ⌈α * S.card⌉₊).card) := by
  obtain ⟨ell,α,C,_,_,hα,hJohnson,hC,N0,hbase,_,hproper,_⟩ :=
    all_rates_certain_failure_full ρ hρ hρ' s hs
  obtain ⟨L,hL⟩ := exists_nat_ge (2 * (1 + C))
  let c : ℝ := 1 / (2 * (1 + C))
  have hlarge (N : ℕ) (hN : max (max N0 L) 1 ≤ N) :
      2 * (1 + C) ≤ (N : ℝ)^s := by
    have hLN : L ≤ N := (le_max_right N0 L).trans ((le_max_left _ _).trans hN)
    have h1 : 1 ≤ N := (le_max_right _ _).trans hN
    exact hL.trans ((by exact_mod_cast hLN : (L : ℝ) ≤ N).trans
      (le_self_pow₀ (by exact_mod_cast h1) (by omega)))
  refine ⟨α,c,hα,hJohnson,by dsimp [c]; positivity,max (max N0 L) 1,?_,?_⟩
  · intro F _ _ _ _ D hD hq
    have hN0 : N0 ≤ (additiveDomain D).card :=
      (le_max_left N0 L).trans ((le_max_left _ _).trans hD)
    obtain ⟨f,g,hg,hcommon,hp,_⟩ := hbase F D hN0
    refine ⟨f,g,hg,hcommon,?_⟩
    have hN : 0 < (additiveDomain D).card := by
      have := (le_max_right _ _).trans hD
      omega
    have hb := all_rates_nonzero_count_of_probability (additiveDomain D)
      ⌊ρ * (additiveDomain D).card⌋₊ ⌈α * (additiveDomain D).card⌉₊ s f g C hN hC hq hp
    have ho := all_rates_omega_from_count _ C _ hC (hlarge _ hD) hb
    simpa only [c,div_eq_mul_inv,mul_comm,one_mul] using ho
  · intro B F _ _ _ _ _ _ _ φ D hD hproperBF hq
    have hN0 : N0 ≤ (additiveDomain D).card :=
      (le_max_left N0 L).trans ((le_max_left _ _).trans hD)
    obtain ⟨f,g,hf,hg,hcommon,hb⟩ := hproper B F φ D hN0 hproperBF
    have hcard : (mappedDomain φ (additiveDomain D)).card = (additiveDomain D).card :=
      card_mappedDomain φ _
    refine ⟨f,g,hf,hg,hcommon,?_⟩
    have hN : 0 < (mappedDomain φ (additiveDomain D)).card := by
      rw [hcard]
      have := (le_max_right _ _).trans hD
      omega
    have hl := all_rates_count_lower_bound _ _ C _
      (pow_pos (by exact_mod_cast hN) _) (by simpa only [hcard] using hq) hC hb
    have ho := all_rates_omega_from_count _ C _ hC (by rw [hcard]; exact hlarge _ hD) hl
    simpa only [c,div_eq_mul_inv,mul_comm,one_mul] using ho

/-- The paragraph after Theorem 4.5, `s=2`: every fixed rate has a uniformly
quadratic nonzero exceptional population whenever the challenge field has
at least `N²` elements. The same pair has exact second-input and common agreement. -/
theorem all_rates_certain_failure_quadratic_count
    (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) :
    ∃ α c : ℝ, ρ < α ∧ α < Real.sqrt ρ ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
        (D : AddSubgroup F), N₀ ≤ (additiveDomain D).card →
        ((additiveDomain D).card : ℝ)^2 ≤ Fintype.card F →
        let S := additiveDomain D
        let J := ⌊ρ * S.card⌋₊
        ∃ f g : S → F, agreementEQ S J g J ∧ commonAgreementEQ S J f g J ∧
          c * (S.card : ℝ)^2 ≤
            (nonzeroBadChallenges S J f g ⌈α * S.card⌉₊).card := by
  obtain ⟨α,c,hα,hJohnson,hc,N0,hbase,_⟩ :=
    all_rates_certain_failure_polynomial_count ρ hρ hρ' 2 (by decide)
  exact ⟨α,c,hα,hJohnson,hc,N0,hbase⟩

end BinaryFieldCounterexamples
