/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module

public import BinaryFieldCounterexamples.Constructions.Gold.DenseFiniteAssembly

/-!
# Gold counts in every larger containing field

The introductory clause following Corollary 5.2 follows from monotonicity
of the finite collision quotient, without requiring the larger field to
contain a previously chosen challenge field.
-/

@[expose] public section
namespace BinaryFieldCounterexamples.Gold

/-- Theorem 5.1's second collision quotient is monotone in the challenge-field
size, proving the larger-extension clause accompanying Corollary 5.2. -/
theorem gold_collision_quotient_mono (N δ L q₀ q : ℕ)
    (hNq : N < q₀) (hqq : q₀ ≤ q) (hL : 1 ≤ L) :
    (L : ℚ) * ((q₀ : ℚ) - N) / ((q₀ : ℚ) - N + (δ : ℚ) * (L - 1)) ≤
    (L : ℚ) * ((q : ℚ) - N) / ((q : ℚ) - N + (δ : ℚ) * (L - 1)) := by
  have hNqQ : (N : ℚ) < q₀ := by exact_mod_cast hNq
  have hqqQ : (q₀ : ℚ) ≤ q := by exact_mod_cast hqq
  have hLQ : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hbudget : (0 : ℚ) ≤ (δ : ℚ) * (L - 1) := by positivity
  have hden₀ : (0 : ℚ) < (q₀ : ℚ) - N + (δ : ℚ) * (L - 1) := by linarith
  have hden : (0 : ℚ) < (q : ℚ) - N + (δ : ℚ) * (L - 1) := by linarith
  rw [div_le_div_iff₀ hden₀ hden]
  have hprod := mul_nonneg (show (0 : ℚ) ≤ L by positivity)
    (mul_nonneg (show (0 : ℚ) ≤ q - q₀ by linarith) hbudget)
  nlinarith only [hprod]

/-- Corollary 5.2's finite larger-extension bridge: whenever `q₀` satisfies
the finite dense collision budget, every containing field of size at least
`q₀` gives the same count lower bound, with exact common agreement. -/
theorem denseGold_finite_every_larger_extension
    {B F : Type*} [Field B] [Fintype B] [CharP B 2]
    [Field F] [Fintype F] [CharP F 2]
    (φ : B →+* F) (D : AddSubgroup B) (c d t q₀ : ℕ)
    (hB : Fintype.card B = 2 ^ (d + c)) (hD : (additiveDomain D).card = 2 ^ d)
    (ht2 : 2 ≤ t) (htd : t ≤ d / 2)
    (hΔ : 1 ≤ d + c - t * (c + if Even d then 1 else 0))
    (h2N : 2 * 2 ^ d ≤ q₀)
    (hqL : q₀ ≤ (2 ^ d / 2 ^ (2 * t)) *
      (2 ^ (2 * t) * (2 ^ (d + c - t * (c + if Even d then 1 else 0)) - 1) *
        gaussianBinomial 4 (d / 2) t))
    (hqq : q₀ ≤ Fintype.card F) :
    let N : ℕ := 2 ^ d
    let T : ℕ := N / 2 - N / 2 ^ (t + 1)
    let δ : ℕ := N / 2 ^ (2 * t)
    let A := mappedDomain φ (additiveDomain D)
    ∃ f g : A → F,
      commonAgreementEQ A (N / 4) f g (N / 4) ∧
      agreementEQ A (N / 4) g (N / 4) ∧
      agreementLE A (N / 4) f (3 * N / 8 - 1) ∧
      (q₀ : ℚ) / (4 * δ) - 1 ≤
        ((nonzeroBadChallenges A (N / 4) f g T).card : ℚ) := by
  classical
  let N := 2 ^ d
  let δ := N / 2 ^ (2 * t)
  let L := 2 ^ (2 * t) * (2 ^ (d + c - t * (c + if Even d then 1 else 0)) - 1) *
    gaussianBinomial 4 (d / 2) t
  have hN : 0 < N := by dsimp [N]; positivity
  have hNq : N < q₀ := by dsimp [N] at hN ⊢; omega
  have hδ : 0 < δ := by
    have he : δ = 2 ^ (d - 2 * t) := by
      dsimp [δ, N]
      exact Nat.pow_div (by omega) (by decide)
    rw [he]; positivity
  have hL : 1 ≤ L := by
    change q₀ ≤ δ * L at hqL
    by_contra hn
    have : L = 0 := by omega
    simp [this] at hqL
    omega
  have hΔ' : 1 ≤ d + c - t * (d + c - d + if Even d then 1 else 0) := by
    simpa only [Nat.add_sub_cancel_left] using hΔ
  have hgold := gold_counting_sharp φ D 0 (d + c) d t
    hB hD ht2 htd hΔ' (hNq.trans_le hqq)
  have ha : affineDomain (additiveDomain D) 0 = additiveDomain D := by
    ext x; simp [affineDomain]
  dsimp only at hgold
  rw [ha] at hgold
  obtain ⟨f, g, hc, hg, hf, hb, _⟩ := hgold
  refine ⟨f, g, hc, hg, hf, ?_⟩
  have hmono := Nat.ceil_mono (gold_collision_quotient_mono N δ L q₀
    (Fintype.card F) hNq hqq hL)
  have hle : (⌈(L : ℚ) * ((q₀ : ℚ) - N) /
      ((q₀ : ℚ) - N + (δ : ℚ) * (L - 1))⌉₊ - 1 : ℕ) ≤
      (nonzeroBadChallenges (mappedDomain φ (additiveDomain D)) (N / 4) f g
        (N / 2 - N / 2 ^ (t + 1))).card := by
    apply (Nat.sub_le _ _).trans (hmono.trans ?_)
    simpa only [N, δ, L, Nat.add_sub_cancel_left] using (le_max_right _ _).trans hb
  exact (gold_energy_count_lower_bound N δ L q₀ hN h2N hδ hqL).trans
    (by exact_mod_cast hle)

end BinaryFieldCounterexamples.Gold
