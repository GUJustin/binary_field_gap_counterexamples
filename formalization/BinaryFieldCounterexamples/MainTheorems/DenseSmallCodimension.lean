/-
Copyright (c) 2026 Binary Field Counterexamples Contributors.
Released under Apache 2.0 license.
-/
module
public import BinaryFieldCounterexamples.MainTheorems.SuperpolynomialNearJohnson
/-!
# Main theorem: Dense Gold bounds at codimension at most three

This is the in-particular clause of Corollary 5.2 (p. 37). At fixed
codimension `c≤3`, the list and distinct nonzero exceptional count have exponent
`d²/8-O_c(d)`, the deficit is `Θ_c(N^(-(1/4:ℝ)))`, the exceptional probability is
`Ω_c(N^(-(1/2:ℝ)))`, and the actual alphabet has size `2^c N`. The complete
quarter-rate pair, list, and two-sided challenge-field contracts are retained.
-/
@[expose] public section
namespace BinaryFieldCounterexamples
/-- Corollary 5.2, in-particular clause: fixed codimension at most three
 specializes the dense count exponent, deficit, probability, and alphabet size.
 Constants and cutoff precede the field and domain; the pair is fixed before
 the distinct nonzero challenges counted by the paper's concrete semantics. -/
theorem superpolynomial_near_johnson_small_codimension (c : ℕ) (hc : c ≤ 3) :
    ∃ A C p : ℝ, 0 < A ∧ 0 < C ∧ 0 < p ∧ ∃ d₀ : ℕ,
    ∀ (d : ℕ), d₀ ≤ d →
    ∀ (B : Type) [Field B] [Fintype B] [DecidableEq B] [CharP B 2],
    Fintype.card B = 2 ^ (d + c) →
    ∀ (D : AddSubgroup B), (additiveDomain D).card = 2 ^ d →
    let N : ℕ := 2 ^ d
    let E : ℝ := (1 / 8) * (d : ℝ) ^ 2
    Fintype.card B = 2^c * N ∧
    ∃ T L : ℕ,
      A * (N : ℝ) ^ (-(1/4:ℝ)) ≤ 1 / 2 - (T : ℝ) / N ∧
      1 / 2 - (T : ℝ) / N ≤ C * (N : ℝ) ^ (-(1/4:ℝ)) ∧
      (2 : ℝ) ^ (E - C * d) ≤ L ∧
      ordinaryList (additiveDomain D) (N / 4) T L ∧
      ∃ (F : Type) (fieldF : Field F) (finiteF : Fintype F),
      letI := fieldF
      letI := finiteF
      ∃ (φ : B →+* F),
      let D' := mappedDomain φ (additiveDomain D)
      ∃ f g : D' → F,
        commonAgreementEQ D' (N / 4) f g (N / 4) ∧
        (2 : ℝ) ^ (E - C * d) ≤
          (nonzeroBadChallenges D' (N / 4) f g T).card ∧
        p * (N : ℝ) ^ (-(1/2:ℝ)) ≤
          ((nonzeroBadChallenges D' (N / 4) f g T).card : ℝ) / Fintype.card F ∧
        (2 : ℝ) ^ (E - C * d) ≤ Fintype.card F ∧
        (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ (E + C * d) := by
  have hcR : (c : ℝ) ≤ 3 := by exact_mod_cast hc
  have hθ : min (1/4:ℝ) (1/((c:ℝ)+1)) = 1/4 := by
    apply min_eq_left
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(c:ℝ)+1)).mpr
    linarith
  have h := superpolynomial_near_johnson c
  dsimp only at h ⊢
  rw [hθ] at h
  obtain ⟨A,C,p,hA,hC,hp,d₀,h⟩ := h
  refine ⟨A,C,p,hA,hC,hp,d₀,?_⟩
  intro d hd B fieldB finiteB decB charB hB D hD
  refine ⟨?_, ?_⟩
  · rw [hB, pow_add, mul_comm]
  · have hh := h d hd B hB D hD
    simpa only [show (1/4:ℝ)*(1-2*(1/4)) = 1/8 by norm_num,
      show (-1:ℝ)+2*(1/4) = -(1/2:ℝ) by norm_num] using hh

end BinaryFieldCounterexamples
